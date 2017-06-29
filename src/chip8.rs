use std::ops::{
    AddAssign, Add,
    SubAssign, Sub,
    ShrAssign,
    ShlAssign,
    Deref, DerefMut,
    Index, IndexMut
};
use std::io::{ Read, Write, Result as IoResult };
use std::fs::File;
use std::fmt;
use std::num;


// Data for sprites 0..F
const FONT_BYTES_PER_CHAR: u8 = 5;
const FONTSET: [u8; 5 * 16] = [
    // 0
    0b11110000,
    0b10010000,
    0b10010000,
    0b10010000,
    0b11110000,
    // 1
    0b00100000,
    0b01100000,
    0b00100000,
    0b00100000,
    0b01110000,
    // 2
    0b11110000,
    0b00010000,
    0b11110000,
    0b10000000,
    0b11110000,
    // 3
    0b11110000,
    0b00010000,
    0b11110000,
    0b00010000,
    0b11110000,
    // 4
    0b10010000,
    0b10010000,
    0b11110000,
    0b00010000,
    0b00010000,
    // 5
    0b11110000,
    0b10000000,
    0b11110000,
    0b00010000,
    0b11110000,
    // 6
    0b11110000,
    0b10000000,
    0b11110000,
    0b10010000,
    0b11110000,
    // 7
    0b11110000,
    0b00010000,
    0b00100000,
    0b01000000,
    0b01000000,
    // 8
    0b11110000,
    0b10010000,
    0b11110000,
    0b10010000,
    0b11110000,
    // 9
    0b11110000,
    0b10010000,
    0b11110000,
    0b00010000,
    0b11110000,
    // A
    0b11110000,
    0b10010000,
    0b11110000,
    0b10010000,
    0b10010000,
    // B
    0b11100000,
    0b10010000,
    0b11100000,
    0b10010000,
    0b11100000,
    // C
    0b11110000,
    0b10000000,
    0b10000000,
    0b10000000,
    0b11110000,
    // D
    0b11100000,
    0b10010000,
    0b10010000,
    0b10010000,
    0b11100000,
    // E
    0b11110000,
    0b10000000,
    0b11110000,
    0b10000000,
    0b11110000,
    // F
    0b11110000,
    0b10000000,
    0b11110000,
    0b10000000,
    0b10000000,
];



type Opcode = u16;

#[derive(Eq, Ord, PartialEq, PartialOrd, Copy, Clone)]
struct MemAddr {
    value: u16,
}

impl fmt::Display for MemAddr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:0>4X}", self.value)
    }
}

impl From<u16> for MemAddr {
    fn from(value: u16) -> Self {
        MemAddr { value: value & 0x0FFF }
    }
}

impl Add<u16> for MemAddr {
    type Output = MemAddr;
    fn add(self, other: u16) -> Self {
        MemAddr::from(self.value + other)
    }
}

impl MemAddr {
    fn to_usize(&self) -> usize { self.value as usize }
    fn to_u16(&self) -> u16 { self.value }
}


struct MemRange {
    lo: MemAddr,
    hi: MemAddr,
}

impl MemRange {
    fn contains(&self, addr: MemAddr) -> bool {
        self.lo <= addr && addr < self.hi
    }

    fn slice_from<'a>(&self, from: &'a mut [u8]) -> &'a mut [u8] {
        &mut from[self.lo.to_usize() .. self.hi.to_usize()]
    }

    fn iter_bytes(&self) -> MemRangeIter {
        MemRangeIter { range: self, offset: 0, step: 1 }
    }

    fn iter_words(&self) -> MemRangeIter {
        MemRangeIter { range: self, offset: 0, step: 2 }
    }
}

struct MemRangeIter<'a> {
    range: &'a MemRange,
    offset: u16,
    step: u16,
}

impl<'a> Iterator for MemRangeIter<'a> {
    type Item = MemAddr;
    fn next(&mut self) -> Option<MemAddr> {
        self.offset += self.step;
        if self.range.contains(self.range.lo + self.offset) {
            Some(self.range.lo + self.offset)
        } else {
            None
        }
    }
}


struct MemMap {
    interp : MemRange,
    fontset: MemRange,
    program: MemRange,
}

macro_rules! mem_range {
    ($lo:expr => $hi:expr) => {
        MemRange {
            lo: MemAddr { value: $lo & 0x0FFF },
            hi: MemAddr { value: $hi & 0x0FFF },
        }
    }
}

const MEMMAP: MemMap = MemMap {
    interp : mem_range!{ 0x000 => 0x1FF },
    fontset: mem_range!{ 0x050 => 0x0A0 },
    program: mem_range!{ 0x200 => 0xFFF },
};


const MEMSIZE: usize = 4 * 1024;  // 4 KiB


struct Memory {
    data: [u8; MEMSIZE],
}

impl Default for Memory {
    fn default() -> Self {
        let mut mem = Memory { data: [0; MEMSIZE] };
        mem.copy_from(&MEMMAP.fontset, &FONTSET);
        mem
    }
}

trait MemoryOps<T> {
    fn load(&self, address: MemAddr) -> T;
    fn store(&mut self, address: MemAddr, value: T);
}

impl MemoryOps<u8> for Memory {
    #[inline]
    fn load(&self, address: MemAddr) -> u8 {
        self.data[address.to_usize()]
    }

    #[inline]
    fn store(&mut self, address: MemAddr, value: u8) {
        self.data[address.to_usize()] = value;
    }
}

impl MemoryOps<u16> for Memory {
    #[inline]
    fn load(&self, address: MemAddr) -> u16 {
        let l: u8 = self.load(address);
        let r: u8 = self.load(address + 1);
        ((l as u16) << 8) | (r as u16)
    }

    #[inline]
    fn store(&mut self, address: MemAddr, value: u16) {
        self.store(address, (value >> 8) as u8);
        self.store(address + 1, value as u8);
    }
}

impl Memory {
    fn copy_from(&mut self, range: &MemRange, source: &[u8]) {
        range.slice_from(&mut self.data).write(source).unwrap();
    }
}


#[derive(Copy, Clone, Default, PartialEq, PartialOrd)]
struct Reg<T> {
    value: T,
}

type Reg8  = Reg<u8>;
type Reg16 = Reg<u16>;


impl<T> Deref for Reg<T> {
    type Target = T;
    fn deref(&self) -> &T { &self.value }
}

impl<T> DerefMut for Reg<T> {
    fn deref_mut<'a>(&'a mut self) -> &'a mut T { &mut self.value }
}

impl<T> From<T> for Reg<T> {
    fn from(value: T) -> Reg<T> {
        Reg::<T> { value: value }
    }
}

impl<T: ShrAssign<T>> ShrAssign<T> for Reg<T> {
    fn shr_assign(&mut self, n: T) { self.value >>= n }
}

impl<T: ShlAssign<T>> ShlAssign<T> for Reg<T> {
    fn shl_assign(&mut self, n: T) { self.value <<= n }
}

impl AddAssign<u8> for Reg8 {
    fn add_assign(&mut self, n: u8) { self.value = self.value.wrapping_add(n) }
}

impl AddAssign<u16> for Reg16 {
    fn add_assign(&mut self, n: u16) { self.value = self.value.wrapping_add(n) }
}

impl SubAssign<u16> for Reg16 {
    fn sub_assign(&mut self, n: u16) { self.value = self.value.wrapping_sub(n) }
}

impl AddAssign for Reg8 {
    fn add_assign(&mut self, r: Reg8) {
        self.value = self.value.wrapping_add(r.value)
    }
}

impl SubAssign for Reg8 {
    fn sub_assign(&mut self, r: Reg8) {
        self.value = self.value.wrapping_sub(r.value)
    }
}

impl Sub for Reg8 {
    type Output = Reg8;
    fn sub(self, r: Reg8) -> Reg8 {
        Reg8 { value: self.value.wrapping_sub(r.value) }
    }
}

impl<T: PartialEq> PartialEq<T> for Reg<T> {
    fn eq(&self, other: &T) -> bool {
        self.value == *other
    }
}


trait RegOps {
    fn to_u16(&self) -> u16;
    fn to_u8(&self) -> u8;
    fn to_mem_addr(&self) -> MemAddr { MemAddr::from(self.to_u16()) }
}

impl RegOps for Reg8 {
    fn to_u16(&self) -> u16 { self.value as u16 }
    fn to_u8(&self) -> u8 { self.value }
}

impl RegOps for Reg16 {
    fn to_u16(&self) -> u16 { self.value }
    fn to_u8(&self) -> u8 { self.value as u8 }
}

impl fmt::LowerHex for Reg8 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
	write!(f, "{:0>2x}", self.value)
    }
}

impl fmt::LowerHex for Reg16 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
	write!(f, "{:0>4x}", self.value)
    }
}


#[derive(Default)]
struct Stack {
    values: [Reg16; 16],
    sp: u8,
}

impl Stack {
    fn push(&mut self, reg: Reg16) {
        if self.sp >= 0xF {
            panic!("stack overflow");
        }
        self.values[self.sp as usize] = reg;
        self.sp += 1;
    }

    fn top(&self) -> &Reg16 {
        &self.values[self.sp as usize]
    }

    fn pop(&mut self) -> Reg16 {
        if self.sp == 0 {
            panic!("stack underflow");
        }
        let top = self.values[self.sp as usize];
        self.sp -= 1;
        top
    }
}

impl Index<u8> for Stack {
    type Output = Reg16;
    fn index(&self, index: u8) -> &Reg16 { &self.values[index as usize] }
}


#[derive(Default)]
struct Regs {
    v: [Reg8; 16],
    i: Reg16,
    pc: Reg16,
    delay_timer: Reg8,
    sound_timer: Reg8,
}

impl Index<u8> for Regs {
    type Output = Reg8;
    fn index(&self, index: u8)-> &Reg8 { &self.v[index as usize] }
}

impl IndexMut<u8> for Regs {
    fn index_mut(&mut self, index: u8) -> &mut Reg8 { &mut self.v[index as usize] }
}


bitflags! {
    pub struct Keys: u16 {
        const KEY_0 = 0b0000_0000_0000_0001;
        const KEY_1 = 0b0000_0000_0000_0010;
        const KEY_2 = 0b0000_0000_0000_0100;
        const KEY_3 = 0b0000_0000_0000_1000;
        const KEY_4 = 0b0000_0000_0001_0000;
        const KEY_5 = 0b0000_0000_0010_0000;
        const KEY_6 = 0b0000_0000_0100_0000;
        const KEY_7 = 0b0000_0000_1000_0000;
        const KEY_8 = 0b0000_0001_0000_0000;
        const KEY_9 = 0b0000_0010_0000_0000;
        const KEY_A = 0b0000_0100_0000_0000;
        const KEY_B = 0b0000_1000_0000_0000;
        const KEY_C = 0b0001_0000_0000_0000;
        const KEY_D = 0b0010_0000_0000_0000;
        const KEY_E = 0b0100_0000_0000_0000;
        const KEY_F = 0b1000_0000_0000_0000;
    }
}

impl Default for Keys {
    fn default() -> Self { Keys::empty() }
}

impl fmt::Display for Keys {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for key in 0x0..0xF {
            if self.contains(Keys::from_bits_truncate(1 << key)) {
                write!(f, "{:X}", key)
            } else {
                write!(f, ".")
            }?;
        }
        Ok(())
    }
}

pub const SCREEN_W: usize = 64;
pub const SCREEN_H: usize = 32;

struct Screen {
    buffer: [u8; SCREEN_W * SCREEN_H],
}

impl Default for Screen {
    fn default() -> Screen {
        Screen { buffer: [0u8; SCREEN_W * SCREEN_H] }
    }
}

impl Screen {
    #[inline]
    fn clear(&mut self) {
        for p in self.buffer.iter_mut() { *p = 0 }
    }

    #[inline]
    fn offset(x: usize, y: usize) -> usize {
        (x % SCREEN_W) + (y % SCREEN_H) * SCREEN_W
    }

    #[inline]
    fn get(&self, x: usize, y: usize) -> u8 {
        self.buffer[Screen::offset(x, y)]
    }

    #[inline]
    fn xor(&mut self, x: usize, y: usize, value: u8) {
        self.buffer[Screen::offset(x, y)] ^= value;
    }
}

impl fmt::Display for Screen {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for (i, v) in self.buffer.iter().enumerate() {
            if i % SCREEN_W == 0 {
                write!(f, "\n")?;
            }
            write!(f, "{}", if *v > 0 { "##" } else { "··" })?;
        }
        Ok(())
    }
}


#[derive(Debug, Clone, Copy)]
enum XyOp {
    Assign  = 0x0, // Vx <- Vy
    BitOr   = 0x1, // Vx |= Vy
    BitAnd  = 0x2, // Vx &= Vy
    BitXor  = 0x3, // Vx ^= Vy
    NumAdd  = 0x4, // Vx += Vy (sets Vf)
    NumSubX = 0x5, // Vx -= Vy (sets Vf)
    BitShr  = 0x6, // Vx >>= 1 (sets Vf)
    NumSubY = 0x7, // Vx = Vy-Vx (sets Vf)
    BitShl  = 0xE, // Vx <<= 1 (sets Vf)
}

impl fmt::Display for XyOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            XyOp::Assign  => write!(f, "LD"),
            XyOp::BitOr   => write!(f, "OR"),
            XyOp::BitAnd  => write!(f, "AND"),
            XyOp::BitXor  => write!(f, "XOR"),
            XyOp::NumAdd  => write!(f, "ADD"),
            XyOp::NumSubX => write!(f, "SUB"),
            XyOp::BitShr  => write!(f, "SHR"),
            XyOp::NumSubY => write!(f, "SUBN"),
            XyOp::BitShl  => write!(f, "SHL"),
        }
    }
}

#[derive(Debug, Clone, Copy)]
enum XnnOp {
    SkipEq  = 0x3, // if (Vx == NN) skip;
    SkipNeq = 0x4, // if (Vx != NN) skip;
    Assign  = 0x6, // Vx = NN
    Add     = 0x7, // Vx += NN
    Rand    = 0xC, // Vx = rand() & NN
}

impl fmt::Display for XnnOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            XnnOp::SkipEq  => write!(f, "SE"),
            XnnOp::SkipNeq => write!(f, "SNE"),
            XnnOp::Assign  => write!(f, "LD"),
            XnnOp::Add     => write!(f, "ADD"),
            XnnOp::Rand    => write!(f, "RND"),
        }
    }
}

#[derive(Debug)]
enum SkipCmp {
    Eq,
    Neq,
}

#[derive(Debug)]
enum Instruction {
    CallRca1802(u16),        // 0nnn
    DispClear,               // 00E0
    Return,                  // 00EE
    Goto(u16),               // 1nnn
    Call(u16),               // 2nnn
    SkipIf(u8, u8, SkipCmp), // 5xy0 | 9xy0
    XNN(u8, u8, XnnOp),      // _xNN
    XY(u8, u8, XyOp),        // 8xyOp
    AssignI(u16),            // Annn
    RelJump(u16),            // Bnnn
    Draw(u8, u8, u8),        // Dxyn
    SkipIfKey(u8, SkipCmp),  // Ex9E | ExA1
    LoadDT(u8),              // Fx07
    WaitKey(u8),             // Fx0A
    StoreDT(u8),             // Fx15
    StoreST(u8),             // Fx18
    AddI(u8),                // Fx1E
    LoadCharAddr(u8),        // Fx29
    StoreBCD(u8),            // Fx33
    StoreRegs(u8),           // Fx55
    LoadRegs(u8),            // Fx65
}

impl Instruction {
    fn encode(&self) -> Opcode {
        match *self {
            Instruction::CallRca1802(nnn)     => 0x0FFF & nnn,
            Instruction::DispClear            => 0x00E0,
            Instruction::Return               => 0x00DD,
            Instruction::Goto(nnn)            => 0x1000 | (0x0FFF & nnn),
            Instruction::Call(nnn)            => 0x2000 | (0x0FFF & nnn),
            Instruction::SkipIf(x, y, ref op) => (0x0F00 & (x as u16) << 8) 
                                               | (0x00F0 & (x as u16) << 4)
                                               | match *op {
                                                   SkipCmp::Eq  => 0x5000,
                                                   SkipCmp::Neq => 0x9000,
                                               },
            Instruction::XNN(x, nn, op)       => (op as u16) << 12
                                               | (0x0F00 & (x as u16) << 8)
                                               | (0x00FF & nn as u16),
            Instruction::XY(x, y, op)         => 0x8000
                                               | (0x0F00 & (x as u16) << 8)
                                               | (0x00F0 & (y as u16) << 4)
                                               | (0x000F & (op as u16)),
            Instruction::AssignI(nnn)         => 0xA000 | (nnn & 0x0FFF),
            Instruction::RelJump(nnn)         => 0xB000 | (nnn & 0x0FFF),
            Instruction::Draw(x, y, n)        => 0xD000
                                               | (0x0F00 & (x as u16) << 8)
                                               | (0x00F0 & (y as u16) << 4)
                                               | (0x000F & (n as u16)),
            Instruction::SkipIfKey(x, ref op) => (0x0F00 & (x as u16) << 8)
                                               | match *op {
                                                   SkipCmp::Eq  => 0xE09E,
                                                   SkipCmp::Neq => 0xE0A1,
                                               },
            Instruction::LoadDT(x)            => 0xF007 | (0x0F00 & (x as u16) << 8),
            Instruction::WaitKey(x)           => 0xF00A | (0x0F00 & (x as u16) << 8),
            Instruction::StoreDT(x)           => 0xF015 | (0x0F00 & (x as u16) << 8),
            Instruction::StoreST(x)           => 0xF018 | (0x0F00 & (x as u16) << 8),
            Instruction::AddI(x)              => 0xF01E | (0x0F00 & (x as u16) << 8),
            Instruction::LoadCharAddr(x)      => 0xF029 | (0x0F00 & (x as u16) << 8),
            Instruction::StoreBCD(x)          => 0xF033 | (0x0F00 & (x as u16) << 8),
            Instruction::StoreRegs(x)         => 0xF055 | (0x0F00 & (x as u16) << 8),
            Instruction::LoadRegs(x)          => 0xF065 | (0x0F00 & (x as u16) << 8),
        }
    }
}

impl fmt::Display for Instruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Instruction::CallRca1802(nnn)     => write!(f, "SYS  0x{:0>4X}", 0x0FFF & nnn),
            Instruction::DispClear            => write!(f, "CLS"),
            Instruction::Return               => write!(f, "RET"),
            Instruction::Goto(nnn)            => write!(f, "JP   0x{:0>4X}", 0x0FFF & nnn),
            Instruction::Call(nnn)            => write!(f, "CALL 0x{:0>4X}", 0x0FFF & nnn),
            Instruction::SkipIf(x, y, ref op) => write!(f, "{:4} V{:X}, V{:X}",
                                                        format!("{}", match *op {
                                                            SkipCmp::Eq  => "SE",
                                                            SkipCmp::Neq => "SNE",
                                                        }), 0xF & x, 0xF & y),
            Instruction::XNN(x, nn, ref op)   => write!(f, "{:4} V{:X}, {}",
                                                        format!("{}", op), 0xF & x, nn),
            Instruction::XY(x, y, ref op)     => write!(f, "{:4} V{:X}, V{:X}",
                                                        format!("{}", op), 0xF & x, 0xF & y),
            Instruction::AssignI(nnn)         => write!(f, "LD   0x{:0>4X}", 0x0FFF & nnn),
            Instruction::RelJump(nnn)         => write!(f, "JP   V0, 0x{:0>4X}", 0xFFF & nnn),
            Instruction::Draw(x, y, n)        => write!(f, "DRW  V{:X}, V{:X}, {}", 0xF & x, 0xF & y, 0xF & n),
            Instruction::SkipIfKey(x, ref op) => write!(f, "{:4} V{:X}", format!("{}", match *op {
                                                            SkipCmp::Eq  => "SKP",
                                                            SkipCmp::Neq => "SKNP",
                                                        }), 0xF & x),
            Instruction::LoadDT(x)            => write!(f, "LD   V{:X}, DT", 0xF & x),
            Instruction::WaitKey(x)           => write!(f, "LD   V{:X}, K",  0xF & x),
            Instruction::StoreDT(x)           => write!(f, "LD   DT, V{:X}", 0xF & x),
            Instruction::StoreST(x)           => write!(f, "LD   ST, V{:X}", 0xF & x),
            Instruction::AddI(x)              => write!(f, "ADD  I,  V{:X}", 0xF & x),
            Instruction::LoadCharAddr(x)      => write!(f, "LD   LF, V{:X}", 0xF & x),
            Instruction::StoreBCD(x)          => write!(f, "LD   B,  V{:X}", 0xF & x),
            Instruction::StoreRegs(x)         => write!(f, "LD   [I], V{:X}", 0xF & x),
            Instruction::LoadRegs(x)          => write!(f, "LD   V{:X}, [I]", 0xF & x),
        }
    }
}


#[derive(Default)]
pub struct Chip8 {
    regs: Regs,
    stack: Stack,
    mem: Memory,
    keys: Keys,
    screen: Screen,
    redraw: bool,
    random: ::rng::XAbcRng,
}

impl Chip8 {
    pub fn new() -> Self {
        Chip8 {
            regs: Regs {
                pc: Reg16::from(0x200),
                ..Default::default()
            },
            ..Default::default()
        }
    }

    pub fn load(&mut self, f: &mut File) {
        let mut v = Vec::new();
        let l = f.read_to_end(&mut v).unwrap();
        self.mem.copy_from(&MEMMAP.program, &v);
    }

    pub fn disassemble<T: Write>(&self, f: &mut T) -> IoResult<()> {
        for addr in MEMMAP.program.iter_words() {
            let op: Opcode = self.mem.load(addr);
            write!(f, "{} [{:0>4X}]: ", addr, op)?;
            write!(f, "{}\n", Chip8::decode(op))?;
        }
        Ok(())
    }

    pub fn cycle(&mut self) {
        // Clear the redraw flag.
        self.redraw = false;
        // Fetch instruction.
        let op: Opcode = self.mem.load(self.regs.pc.to_mem_addr());
        self.regs.pc += 2;
        self.dispatch(Chip8::decode(op));
    }

    pub fn screen<'a>(&'a self) -> &'a [u8] {
        &self.screen.buffer
    }

    fn fflag(&mut self, enabled: bool) {
        *self.regs[0xF] = if enabled { 1 } else { 0 };
    }

    fn decode(op: Opcode) -> Instruction {
        // TODO: Turn panic! into something else.
        match op {
            0x00E0 => Instruction::DispClear,
            0x00EE => Instruction::Return,
            _ => match op >> 12 {
                // Match high byte first
                0x0 => Instruction::CallRca1802(op & 0x0FFF),
                0x1 => Instruction::Goto(op & 0x0FFF),
                0x2 => Instruction::Call(op & 0x0FFF),
                0x3 => Instruction::XNN((op & 0x0F00 >> 8) as u8,
                                        op as u8, XnnOp::SkipEq),
                0x4 => Instruction::XNN((op & 0x0F00 >> 8) as u8,
                                        op as u8,
                                        XnnOp::SkipNeq),
                0x5 => Instruction::SkipIf((op & 0x0F00 >> 8) as u8,
                                           (op & 0x00F0 >> 4) as u8,
                                           SkipCmp::Eq),
                0x6 => Instruction::XNN((op & 0x0F00 >> 8) as u8,
                                        op as u8,
                                        XnnOp::Assign),
                0x7 => Instruction::XNN((op & 0x0F00 >> 8) as u8,
                                        op as u8, XnnOp::Add),
                0x8 => Instruction::XY((op & 0x0F00 >> 8) as u8,
                                       (op & 0x00F0 >> 4) as u8,
                                       match op & 0x000F {
                                           0x0 => XyOp::Assign,
                                           0x1 => XyOp::BitOr,
                                           0x2 => XyOp::BitAnd,
                                           0x3 => XyOp::BitXor,
                                           0x4 => XyOp::NumAdd,
                                           0x5 => XyOp::NumSubX,
                                           0x6 => XyOp::BitShr,
                                           0x7 => XyOp::NumSubY,
                                           0xE => XyOp::BitShl,
                                           _   => panic!("illegal instruction: {:X}", op),
                                       }),
                0x9 => Instruction::SkipIf((op & 0x0F00 >> 8) as u8,
                                           (op & 0x00F0 >> 4) as u8,
                                           SkipCmp::Neq),
                0xA => Instruction::AssignI(op & 0x0FFF),
                0xB => Instruction::RelJump(op & 0x0FFF),
                0xC => Instruction::XNN((op & 0x0F00 >> 8) as u8,
                                         op as u8,
                                         XnnOp::Rand),
                0xD => Instruction::Draw((op & 0x0F00 >> 8) as u8,
                                         (op & 0x00F0 >> 4) as u8,
                                         (op & 0x000F) as u8),
                0xE => {
                    let vreg = (op & 0x0F00 >> 8) as u8;
                    match op & 0x00FF {
                        0x9E => Instruction::SkipIfKey(vreg, SkipCmp::Eq),
                        0xA1 => Instruction::SkipIfKey(vreg, SkipCmp::Neq),
                        _ => panic!("illegal instruction: {:X}", op),
                    }
                },
                0xF => {
                    let vreg = (op & 0x0F00 >> 8) as u8;
                    match op & 0x00FF {
                        0x07 => Instruction::LoadDT(vreg),
                        0x0A => Instruction::WaitKey(vreg),
                        0x15 => Instruction::StoreDT(vreg),
                        0x18 => Instruction::StoreST(vreg),
                        0x1E => Instruction::AddI(vreg),
                        0x29 => Instruction::LoadCharAddr(vreg),
                        0x33 => Instruction::StoreBCD(vreg),
                        0x55 => Instruction::StoreRegs(vreg),
                        0x65 => Instruction::LoadRegs(vreg),
                        _ => panic!("illegal Instruction: {:X}", op),
                    }
                },
                _   => panic!("illegal instruction: {:X}", op),
            }
        }
    }

    fn dispatch(&mut self, insn: Instruction) {
        match insn {
            Instruction::CallRca1802(_) => panic!("unimplemented op: {:?}", insn),
            Instruction::DispClear => self.screen.clear(),
            Instruction::Return => self.regs.pc = self.stack.pop(),
            Instruction::Goto(addr) => *self.regs.pc = addr,
            Instruction::Call(addr) => {
                self.stack.push(self.regs.pc);
                *self.regs.pc = addr;
            },
            Instruction::SkipIf(vx, vy, cmp) => if match cmp {
                SkipCmp::Eq => self.regs[vx] == self.regs[vy],
                SkipCmp::Neq=> self.regs[vx] != self.regs[vy],
            } {
                self.regs.pc += 2;
            },
            Instruction::XNN(vx, nn, op) => match op {
                XnnOp::SkipEq => if self.regs[vx] == nn { self.regs.pc += 2 },
                XnnOp::SkipNeq=> if self.regs[vx] != nn { self.regs.pc += 2 },
                XnnOp::Rand   => *self.regs[vx] = self.random.next() & nn,
                XnnOp::Assign => *self.regs[vx] = nn,
                XnnOp::Add    => self.regs[vx] += nn,
            },
            Instruction::XY(vx, vy, op) => match op {
                XyOp::Assign => *self.regs[vx]  = *self.regs[vy],
                XyOp::BitOr  => *self.regs[vx] |= *self.regs[vy],
                XyOp::BitAnd => *self.regs[vx] &= *self.regs[vy],
                XyOp::BitXor => *self.regs[vx] ^= *self.regs[vy],
                XyOp::NumAdd => {
                    let sum = self.regs[vx].to_u16() + self.regs[vy].to_u16();
                    self.fflag(sum > 0xFF);
                    *self.regs[vx] = sum as u8;
                },
                XyOp::NumSubX => {
                    let vf = self.regs[vx] > self.regs[vy];
                    self.fflag(vf);
                    self.regs[vx] -= self.regs[vy];
                },
                XyOp::BitShr => {
                    let vf = *self.regs[vx] & 0x1 == 0x1;
                    self.fflag(vf);
                    self.regs[vx] >>= 1;
                },
                XyOp::NumSubY => {
                    let vf = self.regs[vy] > self.regs[vx];
                    self.fflag(vf);
                    self.regs[vx] = self.regs[vy] - self.regs[vx];
                },
                XyOp::BitShl => {
                    let vf = *self.regs[vx] >> 7 == 0x1;
                    self.fflag(vf);
                    self.regs[vx] <<= 1;
                },
            },
            Instruction::AssignI(nnn) => *self.regs.i = nnn,
            Instruction::RelJump(nnn) => *self.regs.pc = (nnn + self.regs.v[0].to_u16()) & 0x0FFF,
            Instruction::SkipIfKey(k, cmp) => if match cmp {
                SkipCmp::Eq  =>  self.keys.contains(Keys::from_bits_truncate(1 << k)),
                SkipCmp::Neq => !self.keys.contains(Keys::from_bits_truncate(1 << k)),
            } { self.regs.pc += 2 },
            Instruction::LoadDT(vx) => self.regs[vx] = self.regs.delay_timer,
            Instruction::WaitKey(k) => if !self.keys.contains(Keys::from_bits_truncate(1 << k)) {
                self.regs.pc -= 2; // Step back to the same instruction.
            },
            Instruction::StoreDT(vx) => self.regs.delay_timer = self.regs[vx],
            Instruction::StoreST(vx) => self.regs.sound_timer = self.regs[vx],
            Instruction::AddI(vx) => self.regs.i += self.regs[vx].to_u16(),
            Instruction::StoreBCD(vx) => {
                let mut value = self.regs[vx].to_u8();
                let addr = self.regs.i.to_mem_addr();
                self.mem.store(addr + 0, value / 100);
                value %= 100;
                self.mem.store(addr + 1, value / 10);
                value %= 10;
                self.mem.store(addr + 2, value);
            },
            Instruction::StoreRegs(vx) => {
                let base_addr = self.regs.i.to_mem_addr();
                for (offset, reg) in self.regs.v[0..vx as usize].iter().enumerate() {
                    self.mem.store(base_addr + offset as u16, reg.to_u8());
                }
            },
            Instruction::LoadRegs(vx) => {
                let base_addr = self.regs.i.to_mem_addr();
                for (offset, reg) in self.regs.v[0..vx as usize].iter_mut().enumerate() {
                    **reg = self.mem.load(base_addr + offset as u16);
                }
            },
            Instruction::Draw(vx, vy, lines) => {
                let x = self.regs[vx].to_u8() as usize;
                let y = self.regs[vy].to_u8() as usize;
                let base_addr = self.regs.i.to_mem_addr();
                let mut changed = false;
                for yline in 0..(lines-1) as usize {
                    let line: u8 = self.mem.load(base_addr + yline as u16);
                    for xline in 0..7 {
                        // Bit is set in the line of the sprite.
                        let mask = 1 << (7 - xline);
                        if line & mask == mask {
                            if self.screen.get(x + xline, y + yline) > 0 {
                                self.fflag(true);
                            }
                            self.screen.xor(x + xline, y + yline, 1);
                            self.redraw = true;
                        }
                    }
                }
            },
            Instruction::LoadCharAddr(vreg) => {
                let addr = MEMMAP.fontset.lo + (vreg * FONT_BYTES_PER_CHAR) as u16;
                *self.regs.pc = addr.to_u16();
            },
        }
    }
}

impl fmt::Display for Chip8 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let op: Opcode = self.mem.load(self.regs.pc.to_mem_addr());
        write!(f,
               "{}{:0>4x} V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 VA VB VC VD VE VF  DT ST I    PC   Keys\n Regs ",
               if self.redraw { "*" } else { " " }, op)?;
        for value in self.regs.v.iter() {
            write!(f, "{:x} ", value)?;
        }
        write!(f,
               " {:x} {:x} {:x} {:x} {}\nStack",
               self.regs.delay_timer,
               self.regs.sound_timer,
               self.regs.i,
               self.regs.pc,
               self.keys)?;
        for (i, value) in self.stack.values.iter().enumerate() {
            write!(f, "{}{:x}", if i == self.stack.sp as usize { "`" } else { " " }, value)?;
        }
        if self.redraw {
            write!(f, "\n{}\n", self.screen)?;
        }
        Ok(())
    }
}
