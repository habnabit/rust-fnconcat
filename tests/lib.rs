#![feature(plugin)]
#![plugin(fnconcat)]


fnconcat!{[a, b]() -> u32 {
    9
}}

#[test]
fn test_two_idents() {
    assert_eq!(ab(), 9);
}


fnconcat!{[a, c]<T: std::ops::Add>(p1: T, p2: T) -> T::Output {
    p1 + p2
}}

#[test]
fn test_two_idents_and_type_parameterization() {
    assert_eq!(ac(2, 3), 5);
}


fnconcat!{[[a, d]]() -> u32 {
    13
}}

#[test]
fn test_two_nested_idents() {
    assert_eq!(ad(), 13);
}


fnconcat!{[a, [b, c], d]() -> u32 {
    17
}}

#[test]
fn test_multiple_nested_idents() {
    assert_eq!(abcd(), 17);
}


fnconcat!{[a,,,,e]() -> u32 {
    19
}}

#[test]
fn test_commas_with_nothing_between_them() {
    assert_eq!(ae(), 19);
}


macro_rules! test_macro {
    ($input:ident) => {
        fnconcat!{[$input, extra]() -> u32 {
            23
        }}
    }
}

test_macro!{ok}

#[test]
fn test_ident_built_partially_from_macro() {
    assert_eq!(okextra(), 23);
}


#[test]
fnconcat!{[test_, annotations]() {

}}


parametrize_test!{test_addition, [
    (a: u32, b: u32, r: u32),
    (1, 1, 2),
    (1, 2, 3),
    (2, 2, 4),
], {
    assert_eq!(a + b, r);
}}
