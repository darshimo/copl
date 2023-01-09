use std::{
    collections::HashMap,
    env::{self, Args},
    fs, io,
};

mod common;

mod comparenat1;
mod comparenat2;
mod comparenat3;
mod evalcontml1;
mod evalcontml4;
mod evalml1;
mod evalml2;
mod evalml3;
mod evalml4;
mod evalml5;
mod evalnamelessml3;
mod evalnatexp;
mod namelessml3;
mod nat;
mod polytypingml4;
mod reducenatexp;
mod typingml4;
mod while_;

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
        map.insert("EvalNatExp", evalnatexp::f);
        map.insert("ReduceNatExp", reducenatexp::f);
        map.insert("EvalML1", evalml1::f);
        map.insert("EvalML2", evalml2::f);
        map.insert("EvalML3", evalml3::f);
        map.insert("NamelessML3", namelessml3::f);
        map.insert("EvalNamelessML3", evalnamelessml3::f);
        map.insert("EvalML4", evalml4::f);
        map.insert("EvalML5", evalml5::f);
        map.insert("TypingML4", typingml4::f);
        map.insert("PolyTypingML4", polytypingml4::f);
        map.insert("While", while_::f);
        map.insert("EvalContML1", evalcontml1::f);
        map.insert("EvalContML4", evalcontml4::f);
        map
    };

    let f = map.get(&system)?;

    let filepath = get_arg(&mut args, "input path to file.")?;

    let judgement = fs::read_to_string(filepath)?;

    println!("{}", f(&judgement)?);

    Ok(())
}
