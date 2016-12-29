use std::io::Write;
use asmparse::{
    Register as R,
    Expression as E,
    Instruction as I,
    Item, Directive,
    AsmOption,
};


pub enum Model {
    /// Original CHIP-8.
    CHIP8,
    /// CHIP-48.
    CHIP48,
    /// Super CHIP-48 V1.0.
    SCHIP10,
    /// Super CHIP-48 V1.1.
    SCHIP11,
}


#[inline] fn vx(x: u8) -> u16 { ((x & 0xF) as u16) << 8 }
#[inline] fn vy(y: u8) -> u16 { ((y & 0xF) as u16) << 4 }


pub fn assemble(i: I) -> u16 {
    match i {
        I::ADD(R::I, E::Reg(R::V(x)))    => 0xF013 | vx(x),
        I::ADD(R::V(x), E::Byte(nn))     => 0x7000 | vx(x) | nn as u16,
        I::ADD(R::V(x), E::Reg(R::V(y))) => 0x8004 | vx(x) | vy(y),

        I::CALL(E::Addr(nnn)) => 0x2000 | (0x0FFF & nnn),

        I::OR (R::V(x), R::V(y)) => 0x8001 | vx(x) | vy(y),
        I::AND(R::V(x), R::V(y)) => 0x8002 | vx(x) | vy(y),
        I::XOR(R::V(x), R::V(y)) => 0x8003 | vx(x) | vy(y),
        I::SHR(R::V(x), R::V(y)) => 0x8006 | vx(x) | vy(y),
        I::SHL(R::V(x), R::V(y)) => 0x800E | vx(x) | vy(y),

        I::SCD(E::Nibble(n)) => 0x00C0 | ((n & 0xF) as u16),

        I::CLS  => 0x00E0,
        I::RET  => 0x00EE,
        I::SCR  => 0x00FB,
        I::SCL  => 0x00FC,
        I::EXIT => 0x00FD,
        I::HIGH => 0x00FF,
        I::LOW  => 0x00FE,

        I::RND(R::V(x), E::Byte(nn))
            => 0xC000 | vx(x) | (nn as u16),

        I::DRW(R::V(x), R::V(y), E::Nibble(n))
            => 0xD000 | vx(x) | vy(y) | (n & 0xF) as u16,

        I::JP(E::Void, E::Addr(nnn))         => 0x1000 | (0x0FFF & nnn),
        I::JP(E::Reg(R::V(0)), E::Addr(nnn)) => 0xB000 | (0x0FFF & nnn),

        I::LD(R::I,    E::Addr(nnn))    => 0xA000 | (0x0FFF & nnn),
        I::LD(R::B,    E::Reg(R::V(x))) => 0xF033 | vx(x),
        I::LD(R::DT,   E::Reg(R::V(x))) => 0xF015 | vx(x),
        I::LD(R::F,    E::Reg(R::V(x))) => 0xF029 | vx(x), 
        I::LD(R::HF,   E::Reg(R::V(x))) => 0xF030 | vx(x),
        I::LD(R::R,    E::Reg(R::V(x))) => 0xF075 | vx(x),
        I::LD(R::ST,   E::Reg(R::V(x))) => 0xF018 | vx(x),
        I::LD(R::V(x), E::Byte(nn))     => 0x6000 | vx(x) | (nn as u16),
        I::LD(R::V(x), E::Reg(R::DT))   => 0xF007 | vx(x),
        I::LD(R::V(x), E::Reg(R::K))    => 0xF00A | vx(x),
        I::LD(R::V(x), E::Reg(R::R))    => 0xF085 | vx(x),
        I::LD(R::V(x), E::Reg(R::V(y))) => 0x8000 | vx(x) | vy(y),
        I::LD(R::V(x), E::Reg(R::I))    => 0xF065 | vx(x),
        I::LD(R::I,    E::Reg(R::V(x))) => 0xF055 | vx(x),

        I::SE (R::V(x), E::Byte(nn))     => 0x3000 | vx(x) | (nn as u16),
        I::SNE(R::V(x), E::Byte(nn))     => 0x4000 | vx(x) | (nn as u16),
        I::SE (R::V(x), E::Reg(R::V(y))) => 0x5000 | vx(x) | vy(y),
        I::SNE(R::V(x), E::Reg(R::V(y))) => 0x9000 | vx(x) | vy(y),

        I::SKP (R::V(x)) => 0xE09E | vx(x),
        I::SKNP(R::V(x)) => 0xE0A1 | vx(x),

        I::SYS(E::Addr(nnn)) => 0x0FFF & nnn,

        _ => panic!("invalid operands for instructions: {:?}", i),
    }
}


macro_rules! resolve (
    (@elseif ($_self:ident, $ins:expr) ( $i:ident @ )) => (
        if let I::$i(E::Label(ref name)) = $ins {
            if let Some(&addr) = $_self.labels.get(name) {
                I::$i(E::Addr(addr))
            } else {
                panic!("cannot resolve label '{}'", name)
            }
        }
    );
    (@elseif ($_self:ident, $ins:expr) ( $i:ident _ @ )) => (
        if let I::$i(a, E::Label(ref name)) = $ins {
            if let Some(&addr) = $_self.labels.get(name) {
                I::$i(a, E::Addr(addr))
            } else {
                panic!("cannot resolve label '{}'", name)
            }
        }
    );
    ($_self:ident => $ins:expr => $($tail:tt)*) => {
        $(
            resolve!( @elseif ($_self, $ins) $tail )
        )*
        $ins
    };
);


pub struct Assembler<'a> {
    model: Model,
    labels: ::std::collections::HashMap<String, u16>,
    out: &'a mut Write,
    addr: u16,
    align: bool,
    emit: bool,
}


const DEFAULT_START_ADDR: u16 = 0x200;

impl<'a> Assembler<'a> {
    pub fn new(out: &'a mut Write) -> Self {
        Assembler {
            model: Model::CHIP8,
            labels: ::std::collections::HashMap::new(),
            out: out,
            addr: DEFAULT_START_ADDR,
            align: true,
            emit: false,
        }
    }

    pub fn assemble(&mut self, program: &Vec<Item>) {
        // Pass 1: Gather label addresses.
        self.emit = false;
        self.handle_program(program);
        println!("labels: {:?}", self.labels);
        self.emit = true;
        self.handle_program(program);
    }

    fn handle_program(&mut self, program: &Vec<Item>) {
        for item in program {
            println!("item: {:?}", item);
            match *item {
                Item::Lbl(ref n) => self.handle_label(n),
                Item::Dir(ref d) => self.handle_directive(d),
                Item::Ins(ref i) => self.handle_instruction(i),
                Item::Comment => (),
            }
        }
    }

    fn handle_label(&mut self, name: &str) {
        if !self.emit {
            if let Some(line) = self.labels.get(name) {
                panic!("label '{}' was already defined at line {}", name, line);
            }
            self.labels.insert(name.to_owned(), self.addr);
        }
    }

    fn emit_alignment_byte_if_needed(&mut self) -> ::std::io::Result<()> {
        if self.align && self.addr % 2 == 1 {
            self.addr += 1;
            if self.emit {
                return self.out.write_all(&[0u8]);
            }
        }
        Ok(())
    }

    #[inline]
    fn emit_word(&mut self, word: u16) -> ::std::io::Result<()> {
        if self.emit {
            self.out.write_all(&[(word >> 8) as u8, word as u8])
        } else {
            Ok(())
        }
    }

    fn handle_directive(&mut self, directive: &Directive) {
        match *directive {
            Directive::ALIGN(enable) => self.align = enable,
            Directive::ORG(addr) => self.addr = addr,
            Directive::DB(ref bytes) => {
                // TODO: Check assembly length.
                // TODO: Handle I/O results.
                if self.emit {
                    self.out.write_all(&bytes);
                }
                self.addr += bytes.len() as u16;
                self.emit_alignment_byte_if_needed();
            },
            Directive::DW(ref words) => {
                for word in words {
                    self.emit_word(*word);
                }
                self.addr += words.len() as u16 * 2;
                self.emit_alignment_byte_if_needed();
            },
            Directive::DS(amount) => {
                // TODO: Check assembly length.
                // TODO: Handle I/O results.
                if self.emit {
                    for _ in 0..amount as usize {
                        self.out.write_all(&[0x00]);
                    }
                }
                self.addr += amount as u16;
                self.emit_alignment_byte_if_needed();
            },
            Directive::OPTION(ref opt) => match *opt {
                AsmOption::CHIP8   => self.model = Model::CHIP8,
                AsmOption::CHIP48  => self.model = Model::CHIP48,
                AsmOption::SCHIP10 => self.model = Model::SCHIP10,
                AsmOption::SCHIP11 => self.model = Model::SCHIP11,
                AsmOption::BINARY  => (),
            },
            Directive::XREF(_) => unimplemented!(),
            Directive::USED(_) => unimplemented!(),
        }
    }

    fn handle_instruction(&mut self, instruction: &I) {
        if self.emit {
            let resolved = self.resolve_label(instruction);
            self.emit_word(assemble(resolved));
        } else {
            self.addr += 2;
        }
    }

    fn label_addr(&self, name: &str) -> E {
        if let Some(&addr) = self.labels.get(name) {
            E::Addr(addr)
        } else {
            panic!("undefined label '{}'", name)
        }
    }

    fn resolve_label(&self, instruction: &I) -> I {
        match *instruction {
            I::SYS(E::Label(ref name)) => I::SYS(self.label_addr(&name)),
            I::CALL(E::Label(ref name)) => I::CALL(self.label_addr(name)),
            I::JP(ref r, E::Label(ref name)) => I::JP(r.clone(), self.label_addr(name)),
            I::LD(R::I, E::Label(ref name)) => I::LD(R::I, self.label_addr(name)),
            ref ins => ins.clone(),
        }
    }
}
