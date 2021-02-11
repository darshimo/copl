#[macro_use]
extern crate ruly;

mod evalml1;
mod evalnatexp;
mod nat;
mod tmp;

fn main() {
    let s = "Z * (S(S(Z)) + S(S(Z))) evalto Z";

    evalnatexp::f(s);
}
