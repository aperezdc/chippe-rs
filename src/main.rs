use std::io::{Read, Write};
use std::str::FromStr;

#[macro_use]
extern crate bitflags;

#[macro_use]
extern crate clap;

#[macro_use]
extern crate nom;

mod rng;
mod chip8;
mod asmparse;
mod asm;

fn build_cli() -> ::clap::App<'static, 'static> {
    clap_app!(chipper =>
        (version: "0.1.0")
        (author: "Adrián Pérez <aperez@igalia.com>")
        (about: "CHIP-8 emulator and development tool")
        (@subcommand asm =>
        (about: "Assemble machine code")
            (@arg OUTPUT: -o +takes_value "Write object code to OUTPUT")
            (@arg INPUT: "Path to INPUT file (stdin if not specified)")
        )
        (@subcommand completion =>
            (about: "Generate completion script for SHELL")
            (@arg SHELL: +required "Name of the shell to generate completions for")
        )
    )
}

macro_rules! bail {
    ($code:expr, $( $e:expr ),*) => {{
        write!(::std::io::stderr(), $( $e ),*);
        write!(::std::io::stderr(), "\n");
        ::std::process::exit($code)
    }}
}

fn main() {
    let matches = build_cli().get_matches();
    if let Some(matches) = matches.subcommand_matches("completion") {
        let sh = ::clap::Shell::from_str(matches.value_of("SHELL").unwrap())
            .unwrap_or_else(|_| { bail!(1, "expected one of: {:?}", ::clap::Shell::variants()) });
        build_cli().gen_completions_to("chipper", sh, &mut ::std::io::stdout());
    } else if let Some(matches) = matches.subcommand_matches("asm") {
        let mut input = Vec::new();

        if let Some(filename) = matches.value_of("INPUT") {
            let mut f = ::std::fs::File::open(filename).unwrap();
            f.read_to_end(&mut input).ok();
        } else {
            ::std::io::stdin().read_to_end(&mut input).ok();
        }

        let mut output = Vec::new();
        let program = match asmparse::parse_program(&input) {
            nom::IResult::Done(_, ref program) => {
                println!("program: {:?}", program);
                let mut assembler = asm::Assembler::new(&mut output);
                assembler.assemble(program);
            },
            nom::IResult::Incomplete(_) => unreachable!(),
            nom::IResult::Error(e) => panic!("Error: {:?}", e),
        };

        if let Some(filename) = matches.value_of("OUTPUT") {
            let mut f = ::std::fs::File::create(filename).unwrap();
            f.write_all(&output);
        } else {
            ::std::io::stdout().write_all(&output);
        }
    } else {
        panic!("unknown command");
    }
}
