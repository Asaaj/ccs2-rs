use crate::ast::{AstNode, Key, Nested, Origin, PropDef, Selector};
use pest::{Parser, Span, iterators::Pair};
use pest_derive::Parser;
use std::backtrace::Backtrace;

#[derive(Parser)]
#[grammar = "ast/ccs2.pest"]
struct Ccs2Parser;

#[derive(thiserror::Error, Debug)]
pub enum ParseError {
    #[error("Syntax error: {0}")]
    SyntaxError(#[from] pest::error::Error<Rule>),
    #[error("Unexpected rule: expected {0:?}, got {1:?}")]
    UnexpectedRule(Rule, Rule),
    #[error("Unexpected rule: expected any of {0:?}, got {1:?}")]
    RuleNotInGroup(Vec<Rule>, Rule),
    #[error("Unsupported rule: {rule:?}")]
    UnsupportedRule { rule: Rule, backtrace: Backtrace },
    #[error("Unexpected size: expected {0}, got {1}")]
    UnexpectedSize(usize, usize),
    #[error("Invalid key format: {0}")]
    InvalidKey(String),
    #[error("{0}")]
    Other(String),
}
pub type CcsResult<T> = Result<T, ParseError>;

pub fn parse(file_contents: impl AsRef<str>) -> CcsResult<Nested> {
    let mut file = Ccs2Parser::parse(Rule::file, file_contents.as_ref())?;

    let contents: Pair<Rule> = file.next().unwrap();
    let nested = contents.try_into()?;

    assert_eq!(file.next().map(|p| p.as_rule()), Some(Rule::EOI));

    eprintln!("\n\nCompleted!\n{nested:#?}");
    Ok(nested)
}

macro_rules! expect_rule {
    ($actual:expr, [$exp1:expr $(, $exps:expr)* $(,)?]) => {{
        let expected = vec![$exp1 $(, $exps)*];
        (expected.iter().any(|e| $actual == *e))
            .true_or(ParseError::RuleNotInGroup(expected, $actual))
            .map(|_| {})
    }};
    ($actual:expr, $expected:expr) => {
        ($actual == $expected)
            .true_or(ParseError::UnexpectedRule($expected, $actual))
            .map(|_| {})
    };
}

mod keywords {
    use crate::ast::Import;

    use super::*;

    pub struct Context(pub Selector);
    impl TryFrom<Pair<'_, Rule>> for Context {
        type Error = ParseError;

        fn try_from(value: Pair<'_, Rule>) -> Result<Self, Self::Error> {
            expect_rule!(value.as_rule(), Rule::context_stmt)?;
            Ok(Self(value.into_inner().get_exactly_one()?.try_into()?))
        }
    }

    impl TryFrom<Pair<'_, Rule>> for Import {
        type Error = ParseError;

        fn try_from(value: Pair<'_, Rule>) -> Result<Self, Self::Error> {
            expect_rule!(value.as_rule(), Rule::import_stmt)?;
            let location: Unquoted = value.into_inner().get_exactly_one()?.try_into()?;
            Ok(Self::new(location.0))
        }
    }

    pub struct Constrain(pub nested::SelectorDef);
    impl TryFrom<Pair<'_, Rule>> for Constrain {
        type Error = ParseError;

        fn try_from(value: Pair<'_, Rule>) -> Result<Self, Self::Error> {
            expect_rule!(value.as_rule(), Rule::constrain_stmt)?;
            Ok(Self(value.into_inner().get_exactly_one()?.try_into()?))
        }
    }
}

mod nested {
    use super::*;
    use crate::ast::{Expr, Op};

    impl TryFrom<Pair<'_, Rule>> for Nested {
        type Error = ParseError;

        fn try_from(value: Pair<'_, Rule>) -> Result<Self, Self::Error> {
            let original_rule = value.as_rule();
            expect_rule!(
                original_rule,
                [Rule::ctx_block, Rule::ctx_def, Rule::file_contents]
            )?;
            let mut nested = Nested::default();
            let mut context: Option<keywords::Context> = None;

            let inner = value.into_inner();
            for pair in inner {
                match pair.as_rule() {
                    Rule::context_stmt => {
                        assert!(original_rule == Rule::file_contents);
                        assert!(context.is_none());
                        context = Some(pair.try_into()?);
                    }
                    Rule::constrain_stmt => {
                        let statement: keywords::Constrain = pair.try_into()?;
                        nested.append(AstNode::Constraint(statement.0.0))
                    }
                    Rule::import_stmt => nested.append(AstNode::Import(pair.try_into()?)),
                    Rule::ctx_def => nested.append(AstNode::Nested(pair.try_into()?)),
                    Rule::ctx_block => nested.append(AstNode::Nested(pair.try_into()?)),
                    Rule::selector => nested.set_selector(pair.try_into()?),
                    Rule::prop_def => nested.append(AstNode::PropDef(pair.try_into()?)),
                    _ => todo!("inner-level incomplete: {pair:#?}"),
                }
            }

            if let Some(context) = context {
                eprintln!("Applying context {}", context.0);
                let inner_nested = nested;
                nested = Nested::default();
                nested.set_selector(context.0);
                nested.append(AstNode::Nested(inner_nested));
            }

            Ok(nested)
        }
    }

    /// This builds a chain of selector_components left-associatively, so the resulting expression
    /// is nested from the left.
    ///
    /// Examples:
    /// - `a.b` -> `a.b`
    /// - `(a.b a.c), c.d` -> `OR!(AND!(a.b, a.c), c.d)`
    /// - `c.d, (a.b a.c)` -> `OR!(c.d, AND!(a.b, a.c))`
    /// - `a.b a.c a.d a.e` -> `AND!(AND!(AND!(a.b, a.c), a.d), a.e)`
    impl TryFrom<Pair<'_, Rule>> for Selector {
        type Error = ParseError;

        fn try_from(value: Pair<'_, Rule>) -> Result<Self, Self::Error> {
            expect_rule!(value.as_rule(), Rule::selector)?;

            let mut inner = value.into_inner();

            let left_component: SelectorComponent = inner.next().unwrap().try_into()?;
            let mut left: Selector = left_component.into();

            while let Some(next_piece) = inner.next() {
                match next_piece.as_rule() {
                    Rule::conjunction => {
                        let right: SelectorComponent = inner.next().unwrap().try_into()?;
                        left = Selector::Expr(Expr::new(Op::And, [left, right.into()]));
                    }
                    Rule::disjunction => {
                        let right: SelectorComponent = inner.next().unwrap().try_into()?;
                        left = Selector::Expr(Expr::new(Op::Or, [left, right.into()]));
                    }
                    _ => Err(unsupported(next_piece.as_rule()))?,
                }
            }

            eprintln!("EXPR: {left}");
            Ok(left)
        }
    }

    #[derive(Debug)]
    enum SelectorComponent {
        SelectorDef(SelectorDef),
        Selector(Selector),
    }
    impl TryFrom<Pair<'_, Rule>> for SelectorComponent {
        type Error = ParseError;

        fn try_from(value: Pair<'_, Rule>) -> Result<Self, Self::Error> {
            expect_rule!(value.as_rule(), Rule::selector_component)?;

            let inner = value.into_inner().get_exactly_one()?;
            let res = match inner.as_rule() {
                Rule::selector_def => Self::SelectorDef(inner.try_into()?),
                Rule::selector => Self::Selector(inner.try_into()?),
                _ => Err(unsupported(inner.as_rule()))?,
            };
            Ok(res)
        }
    }
    impl From<SelectorComponent> for Selector {
        fn from(value: SelectorComponent) -> Self {
            match value {
                SelectorComponent::SelectorDef(selector_def) => Self::Step(selector_def.0),
                SelectorComponent::Selector(selector) => selector,
            }
        }
    }

    #[derive(Debug)]
    pub struct SelectorDef(pub Key);
    impl TryFrom<Pair<'_, Rule>> for SelectorDef {
        type Error = ParseError;

        fn try_from(value: Pair<'_, Rule>) -> Result<Self, Self::Error> {
            expect_rule!(value.as_rule(), Rule::selector_def)?;

            Ok(Self(value.into_inner().get_exactly_one()?.try_into()?))
        }
    }

    /// The `a.b` part of `a.b { prop = val }`
    impl TryFrom<Pair<'_, Rule>> for Key {
        type Error = ParseError;

        fn try_from(value: Pair<'_, Rule>) -> Result<Self, Self::Error> {
            expect_rule!(value.as_rule(), Rule::key)?;

            let mut inner = value.into_inner();
            let name: Unquoted = inner.next().unwrap().try_into()?;

            let values = if let Some(value) = inner.next() {
                let value: KeyValue = value.try_into()?;
                vec![value.0.0]
            } else {
                vec![]
            };

            (inner.len() == 0).true_or(ParseError::UnexpectedSize(1, inner.len()))?;
            Ok(Key::new(name.0, values))
        }
    }

    /// The `b` part of `a.b { prop = val }`
    struct KeyValue(Unquoted);
    impl TryFrom<Pair<'_, Rule>> for KeyValue {
        type Error = ParseError;

        fn try_from(value: Pair<'_, Rule>) -> Result<Self, Self::Error> {
            expect_rule!(value.as_rule(), Rule::key_value)?;

            let inner = value.into_inner();
            Ok(Self(inner.get_exactly_one()?.try_into()?))
        }
    }
}

mod prop_def {
    use super::*;

    impl TryFrom<Pair<'_, Rule>> for PropDef {
        type Error = ParseError;

        fn try_from(value: Pair<'_, Rule>) -> Result<Self, Self::Error> {
            expect_rule!(value.as_rule(), Rule::prop_def)?;

            let inner = value.into_inner().get_exactly_one()?;
            match inner.as_rule() {
                Rule::simple_prop_def => Ok(SimplePropDef::try_from(inner)?.0),
                Rule::overridden_prop_def => Ok(OverriddenPropDef::try_from(inner)?.0),
                _ => Err(unsupported(inner.as_rule())),
            }
        }
    }

    struct SimplePropDef(PropDef);
    impl TryFrom<Pair<'_, Rule>> for SimplePropDef {
        type Error = ParseError;

        fn try_from(value: Pair<'_, Rule>) -> Result<Self, Self::Error> {
            expect_rule!(value.as_rule(), Rule::simple_prop_def)?;

            let origin: Origin = value.as_span().into();

            let mut inner = value.into_inner();
            let name: Unquoted = inner.next().unwrap().try_into()?;
            let value: Value = inner.next().unwrap().try_into()?;
            Ok(Self(PropDef {
                name: name.0,
                value: value.0.0,
                origin,
                should_override: false,
            }))
        }
    }

    struct OverriddenPropDef(PropDef);
    impl TryFrom<Pair<'_, Rule>> for OverriddenPropDef {
        type Error = ParseError;

        fn try_from(value: Pair<'_, Rule>) -> Result<Self, Self::Error> {
            expect_rule!(value.as_rule(), Rule::overridden_prop_def)?;

            let simple_prop: SimplePropDef = value.into_inner().get_exactly_one()?.try_into()?;
            Ok(Self(PropDef {
                name: simple_prop.0.name,
                value: simple_prop.0.value,
                origin: simple_prop.0.origin,
                should_override: true,
            }))
        }
    }

    struct Value(Unquoted);
    impl TryFrom<Pair<'_, Rule>> for Value {
        type Error = ParseError;

        fn try_from(value: Pair<'_, Rule>) -> Result<Self, Self::Error> {
            expect_rule!(value.as_rule(), Rule::prop_value)?;
            let value = value.into_inner().get_exactly_one()?;
            Ok(Self(value.try_into()?))
        }
    }
}

/// Utility for flattening a `str` rule, and returning just its unquoted contents
struct Unquoted(String);
impl TryFrom<Pair<'_, Rule>> for Unquoted {
    type Error = ParseError;

    fn try_from(value: Pair<'_, Rule>) -> Result<Self, Self::Error> {
        expect_rule!(value.as_rule(), [Rule::value_str, Rule::selector_str])?;

        let value = value.into_inner().get_exactly_one()?;
        match value.as_rule() {
            Rule::unquoted_value_str
            | Rule::unquoted_selector_str
            | Rule::single_quote_str
            | Rule::double_quote_str => Ok(Self(value.as_str().to_string())),
            _ => Err(unsupported(value.as_rule())),
        }
    }
}

impl<'a> From<Span<'a>> for Origin {
    fn from(value: Span) -> Self {
        let (line_number, _) = value.start_pos().line_col();
        Self {
            filename: "".into(), // TODO: File names can't make it here, unfortunately
            line_number: line_number as u32,
        }
    }
}

trait GetExactlyOne {
    type Item;
    fn get_exactly_one(self) -> CcsResult<Self::Item>;
}
impl<T, I: ExactSizeIterator<Item = T>> GetExactlyOne for I {
    type Item = T;

    fn get_exactly_one(mut self) -> CcsResult<Self::Item> {
        (self.len() == 1).true_or(ParseError::UnexpectedSize(1, self.len()))?;
        Ok(self.next().unwrap())
    }
}

trait TrueOr {
    fn true_or(self, error: ParseError) -> CcsResult<Self>
    where
        Self: Sized;
}
impl TrueOr for bool {
    fn true_or(self, error: ParseError) -> CcsResult<Self> {
        if self { Ok(self) } else { Err(error) }
    }
}

fn expect_rule(actual: Rule, expected: Rule) -> CcsResult<()> {
    (actual == expected)
        .true_or(ParseError::UnexpectedRule(expected, actual))
        .map(|_| {})
}

fn unsupported(rule: Rule) -> ParseError {
    ParseError::UnsupportedRule {
        rule,
        backtrace: Backtrace::force_capture(),
    }
}

#[cfg(test)]
mod tests {
    use super::parse;
    use anyhow::Result;

    macro_rules! __test_suite {
        () => {};
        ({$(#[$attrs:meta])? succ: ($name:ident, $e:literal)}, $($rest:tt,)*) => {
            #[test]
            $(#[$attrs])?
            fn $name() -> Result<()> {
                test_impl($e, true)
            }

            __test_suite!{$($rest,)*}
        };
        ({$(#[$attrs:meta])? fail: ($name:ident, $e:literal)}, $($rest:tt,)*) => {
            #[test]
            $(#[$attrs])?
            fn $name() -> Result<()> {
                test_impl($e, false)
            }
            __test_suite!{$($rest,)*}
        };
    }
    macro_rules! test_suite {
        ($suite_name:ident, $($test_defs:tt,)+) => {
            mod $suite_name {
                use super::*;
                __test_suite!($($test_defs,)+);
            }
        };
    }

    // Most of these tests (and the syntax) were taken from ccs2-py
    test_suite! {
        basic_phrases,
        {succ: (empty, "")},
        {succ: (import_outside_block, "@import 'file'")},
        {fail: (bad_context, "@context (foo x.bar # baz)")},
        {succ: (simple_str_prop, "prop = 'val'")},
        {succ: (simple_str_prop_unquoted, "prop = val")},
        {succ: (simple_block, "elem.id {}")},
        {succ: (unquoted_str, "elem.id {x = abc1}")},
        {succ: (unquoted_str_num_prefix, "elem.id {x = 1abc}")},
        {succ: (simple_prop_in_block, "elem.id {prop = 'val'}")},
        {fail: (bad_override, "elem.id {prop = @override 'hi'}")},
        {succ: (conjunction_int_1, "a blah elem {prop=3}")},
        {succ: (conjunction_int_2, "a.class blah elem.id {prop=3}")},
        {succ: (conjunction_float, "a.class blah elem.id {prop=2.3}")},
        {succ: (conjunction_str, "a.class blah elem.id {prop=\"val\"}")},
        {fail: (conjunction_missing_block, "a.class blah elem.id prop=\"val\" }")},
        {succ: (conjunction_hex_int, "a.class blah elem.id {prop=0xAB12}")},
        {succ: (key_value_with_space, "a.class blah elem. id {prop=2.3}")},
        {succ: (key_value_with_multiple_spaces, "a . class elem.id {prop=\"val\"}")},
        {fail: (lonely_selector, "blah")},
        {fail: (context_after_import, "@import 'file'; @context (foo)")},
        {fail: (invlid_keyword, "@yuno?")},
        {succ: (import_and_constrain, "@import 'file' ; @constrain foo")},
        {succ: (import_in_block, "a.class { @import 'file' }")},
        {fail: (context_in_block, "a.class { @context (foo) }")},
        {succ: (context_outside_block, "@context (foo) a.class { }")},
        {succ: (multiple_props_in_block, "elem.id { prop = 'val'; prop2 = 31337 }")},
        {succ: (prop_val_with_quotes, "prop.'val' { p = 1; }")},
        {succ: (conjunction_disjunction, "a b, c d {p=1}")},
        {succ: (disjunction_conjunction_parens, "(a, b) (c, d) {p=1}")},
        {succ: (multi_disjunction, "a, b, c {p=1}")},
        {succ: (mixed_parens, "a, (b c) d {p=1}")},
        {succ: (value_quotes_simple, "a.\"foo\" {}")},
        {succ: (value_prop_quotes_simple, "a.\"foo\" {'test' = 1}")},
        {succ: (value_prop_quotes_conj, "a.\"foo\" 'bar' {'test' = 1}")},
    }

    test_suite! {
        comments,
        {succ: (single_line, "// single line comment\n")},
        {succ: (single_line_no_newline, "// single line comment nonl")},
        {succ: (multi_line, "/* multi-line\ncomment */")},
        {succ: (inline_with_prop, "prop = /* comment */ 'val'")},
        {succ: (inline_extra_slash, "prop = /*/ comment */ 'val'")},
        {succ: (empty_inline, "prop = /**/ 'val'")},
        {#[ignore] succ: (inline_nested, "prop = /* comment /*nest*/ more */ 'val'")},
        {succ: (inline_after_key, "elem.id /* comment */ {prop = 'val'}")},
        {fail: (inline_not_closed, "elem.id /* comment {prop = 'val'}")},
        {succ: (single_line_before_block, "// comment\nelem { prop = 'val' prop = 'val' }")},
    }

    test_suite! {
        ugly_abutments,
        {fail: (two_properties_touching, "foo {p = 1x = 2}")},
        {succ: (two_properties_with_space, "foo {p = 1x p2 = 2}")},
        {succ: (property_with_quotes_touching, "foo {p = 'x'x = 2}")},
        {succ: (two_properties_with_space_2, "foo {p = 1 x = 2}")},
        {fail: (property_and_key, "value=12asdf.foo {}")},
        {succ: (property_and_key_with_space, "value=12asdf.foo nextsel {}")},
        {succ: (no_spaces_needed, "foo{p=1;x=2}")},
        {fail: (keyword_with_property, "foo{@overridep=1}")},
        {succ: (comment_between_keyword_and_property, "foo{@override /*hi*/ p=1}")},
        {#[ignore] succ: (import_with_quotes, "@import'asdf'")},
        {fail: (import_without_quotes, "@importasdf")},
        {#[ignore] succ: (constrain_with_quotes, "@constrain'asdf'")},
        {fail: (constrain_without_quotes, "@constrainasdf")},
        {succ: (weird_spacing, "@import 'asdf' \n ; \n @constrain asdf \n ; @import 'foo'  ")},
        {succ: (comment_between_import, "@import /*hi*/ 'asdf'")},
        {succ: (comment_between_key_and_block, "env.foo/* some comment */{ }")},
    }

    test_suite! {
        in_file_constraints,
        {succ: (constraint_in_constraint, "a.b: @constrain a.c")},
    }

    test_suite! {
        interpolation, // TODO: Name is wrong
        {succ: (single_quotes, "a = 'hi'")},
        {fail: (missing_close_quote, "a = 'hi")},
        {fail: (missing_close_quote_with_escape, "a = 'hi\\")},
        {#[ignore] fail: (invalid_escape, "a = 'hi\\4 there'")},
        {succ: (mid_string_interpolation, "a = 'h${there}i'")},
        {#[ignore] fail: (missing_bracket, "a = 'h$there}i'")},
        {#[ignore] fail: (dash_in_interpolation, "a = 'h${t-here}i'")},
    }

    test_suite! {
        demo,
        {succ: (demo, "prop = 'val';\nprop2 = 'val2'\nelem.id b.c, c.d : 'prop3'='val3'")},
    }

    fn test_impl(to_parse: &str, should_succeed: bool) -> Result<()> {
        let res = parse(to_parse);
        if should_succeed {
            assert!(res.is_ok(), "Expected success, got error: {res:?}");
        } else {
            assert!(
                matches!(res, Err(super::ParseError::SyntaxError(..))),
                "Expected syntax error, got {res:?}"
            );
        }
        Ok(())
    }
}
