#[macro_use]
extern crate ruly;

mod nat;
mod tmp;

fn main() {
    let s = "S(S(Z)) times S(S(Z)) is S(S(S(S(Z))))";

    nat::f(s);
}
