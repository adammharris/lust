// rustc breaks an `assert!` text of more than 78 bytes over lines with
// its pretty printer: each expression in an inconsistent box indented by
// 4, struct fields and match arms in consistent ones. Each case panics,
// so the texts print.
#[derive(Clone, Copy, PartialEq, Debug)]
struct Opts {
    strikethrough: bool,
    definition_lists: bool,
    directives: bool,
    math: bool,
    width: u32,
}
fn opts() -> Opts {
    Opts { strikethrough: true, definition_lists: true, directives: false, math: false, width: 7 }
}
fn for_options(o: &Opts) -> Opts {
    *o
}
#[derive(Clone, Copy, PartialEq, Debug)]
enum Kind {
    Para,
    SoftBreak,
    OrderedList { numbering: u8, start: Option<u32> },
    Cell(u32),
}
fn kind_of_node(n: u32) -> Kind {
    if n > 1000 { Kind::Para } else { Kind::OrderedList { numbering: 1, start: None } }
}
struct Node {
    kind: Kind,
}
fn nodes() -> Vec<Node> {
    vec![Node { kind: Kind::Para }, Node { kind: Kind::Cell(2) }]
}
fn supports(syntax: u32, gesture: u32) -> bool {
    syntax == gesture + 1000
}
fn syntax_for_language(l: u32) -> u32 {
    l
}
fn language_named(s: &str) -> u32 {
    s.len() as u32
}
fn values() -> Vec<u32> {
    vec![3, 4, 5]
}
fn text_value() -> String {
    "some text that is here".to_string()
}

fn binary_chain() {
    let (first_value, second_value, third_value) = (1, 2, 3);
    assert!(first_value == 2 && second_value == 2 && third_value == 3 && first_value + second_value == 3);
}
fn call_args() {
    assert!(supports(syntax_for_language(language_named("a much longer language name here")), language_named("djot")));
}
fn closure_body() {
    assert!(nodes().iter().all(|n| n.kind != Kind::Para && n.kind != Kind::SoftBreak && n.kind != Kind::Cell(9)));
}
fn struct_fields() {
    assert!(for_options(&Opts { strikethrough: true, definition_lists: false, directives: true, math: false, width: 1 }).math);
}
fn struct_rest() {
    assert!(for_options(&Opts { strikethrough: false, definition_lists: false, ..opts() }) == for_options(&Opts { math: true, ..opts() }));
}
fn match_arms() {
    assert!(match values().len() { 0 => false, 1 | 2 => text_value().is_empty(), _ => text_value().starts_with("zzz") });
}
fn if_else() {
    assert!(if text_value().contains("text") { values().iter().any(|&v| v > 100000) } else { supports(1, 2) && supports(3, 4) });
}
fn matches_macro() {
    assert!(matches!(kind_of_node(values().iter().map(|v| v * 3).sum::<u32>()), Kind::OrderedList { numbering: 9, .. }));
}
fn long_string() {
    assert!(text_value() == "a string literal that is much longer than the seventy-eight byte margin of the printer");
}
fn block_let() {
    assert!({ let the_long_variable_name = values().iter().copied().sum::<u32>(); the_long_variable_name > 100000 });
}
fn typed_closure() {
    assert!(values().iter().any(|v: &u32| -> bool { *v > language_named("a much longer language name here") * 100 }));
}
fn macro_operand_in_arm() {
    let x = values().len();
    assert!(match x { 3 => matches!(kind_of_node(7), Kind::Cell(c) if c == 2) || x > 5000, _ => false } && x == 3);
}
fn nested_deep() {
    assert!(supports(syntax_for_language([1, 42, 7].len() as u32 * values().iter().map(|v| v * 4).sum::<u32>()), 1 * language_named("djot")));
}

fn main() {
    let cases: [fn(); 13] = [
        binary_chain,
        call_args,
        closure_body,
        struct_fields,
        struct_rest,
        match_arms,
        if_else,
        matches_macro,
        long_string,
        block_let,
        typed_closure,
        macro_operand_in_arm,
        nested_deep,
    ];
    for case in cases {
        assert!(std::panic::catch_unwind(case).is_err());
    }
    println!("done");
}
