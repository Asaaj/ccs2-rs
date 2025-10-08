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
    let pairs: Vec<Pair<Rule>> = Ccs2Parser::parse(Rule::file, file_contents.as_ref())?.collect();
    let mut nested = Nested::default();

    for pair in pairs {
        match pair.as_rule() {
            Rule::selector => {
                let selector: Selector = pair.try_into()?;
                todo!("SELECTOR: {selector:#?}");
            }
            Rule::ctx_block => nested.append(AstNode::Nested(pair.try_into()?)),
            Rule::prop_def => nested.append(AstNode::PropDef(pair.try_into()?)),
            Rule::EOI => eprintln!("EOI encountered"),
            _ => todo!("outer-level incomplete: {pair:#?}"),
        }
        // let inner: Nested = pair.try_into()?;
        // nested.rules.extend(inner.rules.into_iter());
    }
    eprintln!("\n\nCompleted!\n{nested:#?}");
    Ok(nested)
}

mod nested {
    use crate::ast::Specificity;

    use super::*;

    impl TryFrom<Pair<'_, Rule>> for Nested {
        type Error = ParseError;

        fn try_from(value: Pair<'_, Rule>) -> Result<Self, Self::Error> {
            // expect_rule(value.as_rule(), Rule::ctx_block)?;
            let mut nested = Nested::default();

            let inner = value.into_inner();
            for pair in inner {
                match pair.as_rule() {
                    Rule::selector => {
                        nested.set_selector(pair.try_into()?);
                    }
                    Rule::ctx_block => nested.append(AstNode::Nested(pair.try_into()?)),
                    Rule::prop_def => nested.append(AstNode::PropDef(pair.try_into()?)),
                    Rule::EOI => eprintln!("EOI encountered"),
                    _ => todo!("inner-level incomplete: {pair:#?}"),
                }
            }

            Ok(nested)
        }
    }

    impl TryFrom<Pair<'_, Rule>> for Selector {
        type Error = ParseError;

        fn try_from(value: Pair<'_, Rule>) -> Result<Self, Self::Error> {
            expect_rule(value.as_rule(), Rule::selector)?;

            eprintln!("SELECTOR: {value:#?}");
            let inner = value.into_inner().get_exactly_one()?;
            match inner.as_rule() {
                Rule::selector_def => {
                    let mut inner = inner.into_inner();

                    let first_key: Key = inner.next().unwrap().try_into()?;

                    if let Some(continuation) = inner.next() {
                        todo!("Not parsed: {continuation:#?}");
                    } else {
                        Ok(Selector::Step(first_key))
                    }
                }
                Rule::selector_group => {
                    todo!()
                }
                rule => Err(unsupported(rule)),
            }
        }
    }

    /// The `a.b` part of `a.b { prop = val }`
    impl TryFrom<Pair<'_, Rule>> for Key {
        type Error = ParseError;

        fn try_from(value: Pair<'_, Rule>) -> Result<Self, Self::Error> {
            expect_rule(value.as_rule(), Rule::key)?;

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
            expect_rule(value.as_rule(), Rule::key_value)?;

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
            expect_rule(value.as_rule(), Rule::prop_def)?;

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
            let origin: Origin = value.as_span().into();

            let mut inner = value.into_inner();
            let name: Unquoted = inner.next().unwrap().try_into()?;
            let value: Value = inner.next().unwrap().try_into()?;
            Ok(Self(PropDef {
                name: name.0,
                value: value.0.0,
                origin,
                should_override: true,
            }))
        }
    }

    struct Value(Unquoted);
    impl TryFrom<Pair<'_, Rule>> for Value {
        type Error = ParseError;

        fn try_from(value: Pair<'_, Rule>) -> Result<Self, Self::Error> {
            expect_rule(value.as_rule(), Rule::prop_value)?;
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
        expect_rule(value.as_rule(), Rule::str)?;

        let value = value.into_inner().get_exactly_one()?;
        match value.as_rule() {
            Rule::unquoted_str | Rule::single_quote_str | Rule::double_quote_str => {
                Ok(Self(value.as_str().to_string()))
            }
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
        {succ: (import, "@import 'file'")},
        {fail: (bad_context, "@context (foo x.bar # baz)")},
        {succ: (simple_str_prop, "prop = 'val'")},
        {succ: (simple_str_prop_unquoted, "prop = val")},
        {succ: (simple_block, "elem.id {}")},
        {succ: (unquoted_str, "elem.id {x = abc1}")},
        {succ: (unquoted_str_num_prefix, "elem.id {x = 1abc}")},
        {succ: (simple_prop_in_block, "elem.id {prop = 'val'}")},
        {fail: (bad_override, "elem.id {prop = @override 'hi'}")},
        {succ: (conjunction_int, "a.class blah elem.id {prop=3}")},
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
        {succ: (demo, "prop = 'val';\nprop2 = 'val2'\nelem.id {'prop3'='val3'}")},
    }

    fn test_impl(to_parse: &str, should_succeed: bool) -> Result<()> {
        let res = parse(to_parse);
        assert_eq!(
            res.is_ok(),
            should_succeed,
            "Unexpected parse output: {res:#?}"
        );
        Ok(())
    }
}
