mod words;

pub struct Greeter {
    name: String,
}

impl Greeter {
    pub fn new(name: &str) -> Greeter {
        Greeter { name: name.to_string() }
    }
    pub fn line(&self) -> String {
        format!("{}, {}!", words::HELLO, self.name)
    }
}

pub fn shout(g: &Greeter) -> String {
    g.line().to_uppercase()
}
