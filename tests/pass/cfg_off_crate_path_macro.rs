// A cfg-disabled item still parses, and a macro call by a path that
// starts at `crate`, `self`, or `super` is an opaque call there, in
// expression, statement, type, pattern, and item positions.
#[macro_export]
macro_rules! err {
    ($n:ident) => {
        stringify!($n)
    };
}

fn main() {
    println!("{}", err!(Live));
}

#[cfg(test)]
mod tests {
    fn tail() -> &'static str {
        crate::err!(NotFound)
    }
    fn stmt() {
        crate::err!(Stmt);
        let _x: self::super::Ty![u8] = super::err!(Let);
        match 1 {
            crate::pat!() => {}
            _ => {}
        }
    }
    crate::items!();
    trait T {
        crate::trait_items!();
    }
    impl T for u8 {
        super::impl_items!();
    }
}
