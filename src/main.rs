#[macro_use]
extern crate ruly;

mod evalml1;
mod nat;
mod tmp;

fn main() {
    let s = "3 + (if -23 < -2 * 8 then 8 else 2) + 4 evalto 15";

    evalml1::f(s);
}
