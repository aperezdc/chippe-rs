#[macro_use]
extern crate bitflags;

mod chip8;

fn main() {
    let mut chip = chip8::Chip8::new();
    print!("{}", chip);
}
