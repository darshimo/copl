use std::{
    collections::HashMap,
    env::{self, Args},
    fs, io,
};

mod comparenat1;
mod comparenat2;
mod comparenat3;
mod nat;

struct Map(HashMap<&'static str, fn(&str) -> io::Result<String>>);
impl Map {
    fn new() -> Self {
        Map(HashMap::new())
    }

    fn insert(&mut self, system: &'static str, f: fn(&str) -> io::Result<String>) {
        self.0.insert(system, f);
    }

    fn get(&self, system: &str) -> io::Result<&for<'r> fn(&'r str) -> io::Result<String>> {
        if let Some(f) = self.0.get(system) {
            Ok(f)
        } else {
            Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!("No such system: {}", system),
            ))
        }
    }
}

fn get_arg(args: &mut Args, error_message: &str) -> io::Result<String> {
    if let Some(s) = args.next() {
        Ok(s)
    } else {
        Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            error_message.to_string(),
        ))
    }
}

fn main() -> io::Result<()> {
    let mut args = env::args();
    args.next();

    let system = get_arg(&mut args, "input system name.")?;

    let map = {
        let mut map = Map::new();
        map.insert("Nat", nat::f);
        map.insert("CompareNat1", comparenat1::f);
        map.insert("CompareNat2", comparenat2::f);
        map.insert("CompareNat3", comparenat3::f);
        map
    };

    let f = map.get(&system)?;

    let filepath = get_arg(&mut args, "input path to file.")?;

    let judgement = fs::read_to_string(filepath)?;

    println!("{}", f(&judgement)?);

    Ok(())
}
