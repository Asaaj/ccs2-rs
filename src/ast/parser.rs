use pest_derive::Parser;

#[derive(Parser)]
#[grammar = "ast/ccs2.pest"]
struct Ccs2Parser;

#[cfg(test)]
mod tests {
    use super::{Ccs2Parser, Rule};
    use anyhow::Result;
    use pest::Parser;

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
        {succ: (value_prop_quotes, "a.\"foo\" 'bar' {'test' = 1}")},
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

    fn test_impl(to_parse: &str, should_succeed: bool) -> Result<()> {
        let res = Ccs2Parser::parse(Rule::file, to_parse);
        assert_eq!(res.is_ok(), should_succeed, "Unexpected parse output: {res:?}");
        Ok(())
    }
}
