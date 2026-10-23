// `{:#?}` of a context error quotes the context with
// `str::escape_debug`: quotes, controls, and a combining mark that
// starts the text (escaped) or follows a letter (kept).
use anyhow::{Context, Result};

fn fail(ctx: &'static str) -> Result<()> {
    Err(std::fmt::Error).context(ctx)
}

fn main() {
    for ctx in ["say \"hi\" and 'bye'", "tab\there\nnewline", "e\u{301}t\u{e9}", "\u{301}start", "nul\0 bell\u{7} del\u{7f}", "zero\u{200b}width"] {
        let e = fail(ctx).unwrap_err();
        println!("{e:#?}");
        println!("{e:?}");
    }
    let e = fail("a").unwrap_err().context(format!("{} {}", "x\u{301}", '"'));
    println!("{e:#?}");
}
