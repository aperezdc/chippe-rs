use std::str::FromStr;
use super::nom::*;

#[derive(Debug, PartialEq, Copy, Clone)]
pub enum Register {
    I,
    K,     // Pseudo register for "LD Vx, K"
    B,     // Pseudo register for "LD B, Vx"
    F,     // Pseudo register for "LD F, Vx"
    R,     // Pseudo register for "LD R, Vx"
    HF,    // Pseudo Register for "LD HF, Vx"
    DT,
    ST,
    V(u8),
}


#[derive(Debug, PartialEq, Clone)]
pub enum Expression {
    Void,
    Addr(u16),  // 12-bit
    Label(String),
    Byte(u8),
    Nibble(u8), //  4-bit
    Reg(Register),
}

impl Expression {
    fn from_u16(value: u16) -> Self {
        if value & 0xFFF0 == 0 {
            Expression::Nibble(value as u8)
        } else if value & 0xFF00 == 0 {
            Expression::Byte(value as u8)
        } else if value & 0xF000 == 0 {
            Expression::Addr(value)
        } else {
            // TODO: Better error handling.
            panic!("more than 12-bits used")
        }
    }
}


#[derive(Debug, PartialEq, Clone)]
pub enum Instruction {
    // Fx1E  ADD  I, Vx
    // 7xkk  ADD  Vx, Byte
    // 8xy4  ADD  Vx, Vy
    ADD(Register, Expression),

    // 2nnn  CALL Addr
    CALL(Expression),

    // 8xy2  AND  Vx, Vy
    AND(Register, Register),

    // 00E0  CLS
    CLS,

    // Dxyn  DRW  Vx, Vy, Nibble
    // Dxy0  DRW  Vx, Vy, 0        [+SCHIP1x]
    DRW(Register, Register, Expression),

    // 00FD  EXIT                  [+SCHIP1x]
    EXIT,

    // 00FF  HIGH                  [+SCHIP1x]
    HIGH,

    // 1nnn  JP  Addr
    // Bnnn  JP  V0, Addr
    JP(Expression, Expression),

    // Annn  LD  I,  nnn
    // Fx33  LD  B,  Vx
    // Fx15  LD  DT, Vx
    // Fx29  LD  F,  Vx   [-SCHIP1x]
    //    -  LD  LF, Vx   [+SCHIP1x]
    // Fx30  LD  HF, Vx   [+SCHIP1x]
    // Fx75  LD  R,  Vx   [+SCHIP1x]
    // Fx18  LD  ST, Vx
    // 6xkk  LD  Vx, Byte
    // Fx07  LD  Vx, DT
    // Fx0A  LD  Vx, K
    // Fx85  LD  Vx, R    [+SCHIP1x]
    // 8xy0  LD  Vx, Vy
    // Fx65  LD  Vx, [I]
    // Fx55  LD  [I], Vx
    LD(Register, Expression),

    // 00FE  LOW          [+SCHIP1x]
    LOW,

    // 8xy1  OR  Vx, Vy
    OR(Register, Register),

    // 00EE  RET
    RET,

    // Cxkk  RND  Vx, Byte
    RND(Register, Expression),

    // 00Cn  SCD  Nibble  [+SCHIP11]
    SCD(Expression),

    // 00FC  SCL          [+SCHIP11]
    SCL,

    // 00FB  SCR          [+SCHIP11]
    SCR,

    // 3xkk  SE  Vx, Byte
    // 5xy0  SE  Vx, Vy
    SE(Register, Expression),

    // 8xyE  SHL Vx [, Vy]
    SHL(Register, Register),

    // 8xy6  SHR Vx [, Vy]
    SHR(Register, Register),

    // Ex9E  SKP Vx
    SKP(Register),

    // ExA1  SKNP Vx
    SKNP(Register),

    // 4xkk  SNE  Vx, Byte
    // 9xy0  SNE  Vx, Vy
    SNE(Register, Expression),

    // 8xy5  SUB  Vx, Vy
    SUB(Register, Register),

    // 8xy7  SUBN Vx, Vy
    SUBN(Register, Register),

    // 0NNN  SYS  Addr   [CHIP8]
    SYS(Expression),

    // 8xy3  XOR  Vx, Vy
    XOR(Register, Register),
}


#[derive(Debug, PartialEq)]
pub enum AsmOption {
    BINARY,
    CHIP8,
    CHIP48,
    SCHIP10,
    SCHIP11,
}


#[derive(Debug, PartialEq)]
pub enum QuadState { NO, OFF, ON, YES }


#[derive(Debug, PartialEq)]
pub enum Directive {
    // TODO: EQU(String, _)
    ALIGN(bool),
    // TODO: DA(String)
    DB(Vec<u8>),
    // TODO: DEFINE(String)
    DS(u8),
    DW(Vec<u16>),
    // TODO: ELSE
    // TODO: END
    // TODO: ENDIF
    // TODO: IFDEF
    // TODO: IFUND
    // TODO: INCLUDE(String)
    OPTION(AsmOption),    
    // TODO: OPTION(String)
    ORG(u16),  // XXX: Maybe use Expression(::Addr)
    // TODO: UNDEF(String)
    USED(QuadState),
    // TODO: USEDSymbols(Vec<String>),
    XREF(QuadState),
}


named!(parse_on_off<bool>,
    alt_complete!(
        tag_no_case!("off") => { |_| false } |
        tag_no_case!("on")  => { |_| true  }
    )
);

named!(parse_quad_state<QuadState>,
    alt_complete!(
        tag_no_case!("off") => { |_| QuadState::OFF } |
        tag_no_case!("yes") => { |_| QuadState::YES } |
        tag_no_case!("no")  => { |_| QuadState::NO  } |
        tag_no_case!("on")  => { |_| QuadState::ON  }
    )
);

named!(parse_d_align<Directive>,
    ws!(preceded!(
        tag_no_case!("align"),
        map!(parse_on_off, Directive::ALIGN)
    ))
);

named!(parse_d_db<Directive>,
    ws!(preceded!(
        tag_no_case!("db"),
        map!(separated_nonempty_list!(tag!(","), parse_byte), Directive::DB)
    ))
);

named!(parse_d_ds<Directive>,
    ws!(preceded!(
        tag_no_case!("ds"),
        map!(parse_byte, Directive::DS)
    ))
);

named!(parse_d_dw<Directive>,
    ws!(preceded!(
        tag_no_case!("dw"),
        map!(separated_nonempty_list!(tag!(","), parse_word), Directive::DW)
    ))
);

named!(parse_d_org<Directive>,
    ws!(preceded!(
        tag_no_case!("org"),
        map!(parse_word, Directive::ORG)
    ))
);

named!(parse_d_used<Directive>,
    ws!(preceded!(
        tag_no_case!("used"),
        map!(parse_quad_state, Directive::USED)
    ))
);

named!(parse_d_xref<Directive>,
    ws!(preceded!(
        tag_no_case!("xref"),
        map!(parse_quad_state, Directive::XREF)
    ))
);

named!(parse_d_option<Directive>,
    ws!(preceded!(
        tag_no_case!("option"),
        alt_complete!(
            tag_no_case!("binary")  => { |_| Directive::OPTION(AsmOption::BINARY)  } |
            tag_no_case!("chip8")   => { |_| Directive::OPTION(AsmOption::CHIP8)   } |
            tag_no_case!("chip48")  => { |_| Directive::OPTION(AsmOption::CHIP48)  } |
            tag_no_case!("schip10") => { |_| Directive::OPTION(AsmOption::SCHIP10) } |
            tag_no_case!("schip11") => { |_| Directive::OPTION(AsmOption::SCHIP11) }
        )
    ))
);

named!(parse_directive<Directive>,
    alt_complete!(
        parse_d_align |
        parse_d_db    |
        parse_d_ds    |
        parse_d_dw    |
        parse_d_org   |
        parse_d_used  |
        parse_d_xref  |
        parse_d_option
    )
);

named!(parse_label<&str>,
    map_res!(take_while1!(is_alphabetic), ::std::str::from_utf8)
);

named!(parse_label_def<&str>,
    ws!(terminated!(parse_label, tag!(":")))
);

named!(parse_vreg<Register>,
    preceded!(
        tag_no_case!("v"),
        map!(
            one_of!("0123456789abcdefABCDEF"),
            |r: char| Register::V(r.to_digit(16).unwrap() as u8)
        )
    )
);

// TODO: Error when high bits are set.
named!(parse_nibble<Expression>,
    map!(parse_byte, |b| Expression::Nibble(b & 0x0F))
);


macro_rules! gen_hexdec_number_parser {
    ($name:ident, $name_dec:ident, $name_hex:ident, $t:ident) => {
        named!($name_dec<$t>,
            do_parse!(
                digits: take_while1!(is_digit) >> ({
                    let s = ::std::str::from_utf8(digits).unwrap();
                    $t::from_str_radix(s, 10).unwrap()
                })
            )
        );
        named!($name_hex<$t>,
            do_parse!(
                tag_no_case!("0x") >>
                digits: take_while1!(is_hex_digit) >> ({
                    let s = ::std::str::from_utf8(digits).unwrap();
                    $t::from_str_radix(s, 16).unwrap()
                })
            )
        );
        named!($name<$t>, alt_complete!($name_hex | $name_dec));
    }
}

gen_hexdec_number_parser!(parse_byte, parse_dec_byte, parse_hex_byte, u8);
gen_hexdec_number_parser!(parse_word, parse_dec_word, parse_hex_word, u16);


named!(parse_i_add<Instruction>,
    ws!(preceded!(
        tag_no_case!("add"),
        alt_complete!(
            do_parse!(
                tag_no_case!("i") >> tag!(",") >> vx: parse_vreg >>
                (Instruction::ADD(Register::I, Expression::Reg(vx)))
            ) |
            do_parse!(
                vx: parse_vreg >> tag!(",") >> rhs: alt_complete!(
                        map!(parse_vreg, Expression::Reg) |
                        map!(parse_byte, Expression::Byte)
                    ) >>
                (Instruction::ADD(vx, rhs))
            )
        )
    ))
);


// TODO: Parse labels.
named!(parse_addr<Expression>,
    alt_complete!(
        parse_word  => { Expression::Addr } |
        parse_label => { |s| Expression::Label(String::from(s)) }
    )
);


named!(parse_i_call<Instruction>,
    ws!(do_parse!(
        tag_no_case!("call") >> addr: parse_addr >> (Instruction::CALL(addr))
    ))
);

named!(parse_i_and<Instruction>,
    ws!(do_parse!(
        tag_no_case!("and") >> vx: parse_vreg >> tag!(",") >> vy: parse_vreg >>
        (Instruction::AND(vx, vy))
    ))
);

named!(parse_i_cls<Instruction>,
    do_parse!(tag_no_case!("cls") >> (Instruction::CLS))
);

named!(parse_i_drw<Instruction>,
    ws!(do_parse!(
        tag_no_case!("drw") >> vx: parse_vreg >>
        tag!(",") >> vy: parse_vreg >>
        tag!(",") >> nb: parse_nibble >>
        (Instruction::DRW(vx, vy, nb))
    ))
);

named!(parse_i_exit<Instruction>,
    do_parse!(tag_no_case!("exit") >> (Instruction::EXIT))
);

named!(parse_i_high<Instruction>,
    do_parse!(tag_no_case!("high") >> (Instruction::HIGH))
);

named!(parse_i_jp<Instruction>,
    ws!(preceded!(
        tag_no_case!("jp"),
        alt_complete!(
            do_parse!(
                vx: parse_vreg >> tag!(",") >> addr: parse_addr >>
                (Instruction::JP(Expression::Reg(vx), addr))
            ) |
            do_parse!(
                addr: parse_addr >>
                (Instruction::JP(Expression::Void, addr))
            )
        )
    ))
);   

named!(parse_i_ld<Instruction>,
    ws!(preceded!(
        tag_no_case!("ld"),
        alt_complete!(
            do_parse!( // LD I, nnn
                tag_no_case!("i") >> tag!(",") >> addr: parse_addr >>
                (Instruction::LD(Register::I, addr))
            ) |
            do_parse!( // LD B, Vx
                tag_no_case!("b") >> tag!(",") >> vx: parse_vreg >>
                (Instruction::LD(Register::B, Expression::Reg(vx)))
            ) |
            do_parse!( // LD DT, Vx
                tag_no_case!("dt") >> tag!(",") >> vx: parse_vreg >>
                (Instruction::LD(Register::DT, Expression::Reg(vx)))
            ) |
            do_parse!( // LD F, Vx
                tag_no_case!("f") >> tag!(",") >> vx: parse_vreg >>
                (Instruction::LD(Register::F, Expression::Reg(vx)))
            ) |
            do_parse!( // LD LF, Vx
                tag_no_case!("lf") >> tag!(",") >> vx: parse_vreg >>
                (Instruction::LD(Register::F, Expression::Reg(vx)))
            ) |
            do_parse!( // LD HF, Vx
                tag_no_case!("hf") >> tag!(",") >> vx: parse_vreg >>
                (Instruction::LD(Register::HF, Expression::Reg(vx)))
            ) |
            do_parse!( // LD R, Vx
                // TODO: Check that Vx has x < 7.
                tag_no_case!("r") >> tag!(",") >> vx: parse_vreg >>
                (Instruction::LD(Register::R, Expression::Reg(vx)))
            ) |
            do_parse!( // LD ST, Vx
                tag_no_case!("st") >> tag!(",") >> vx: parse_vreg >>
                (Instruction::LD(Register::ST, Expression::Reg(vx)))
            ) |
            do_parse!( // LD [I], Vx
                tag!("[") >> tag_no_case!("I") >> tag!("]") >>
                tag!(",") >> vx: parse_vreg >>
                (Instruction::LD(Register::I, Expression::Reg(vx)))
            ) |
            do_parse!( // LD Vx, ...
                vx: parse_vreg >> tag!(",") >>
                expr: alt_complete!(
                        tag_no_case!("dt") => {|_| Expression::Reg(Register::DT) } |
                        tag_no_case!("k") => {|_| Expression::Reg(Register::K) } |
                        tag_no_case!("r") => {|_| Expression::Reg(Register::R) } |
                        do_parse!(
                            tag!("[") >> tag_no_case!("i") >> tag!("]") >>
                            (Expression::Reg(Register::I))
                        ) |
                        map!(parse_vreg, Expression::Reg) |
                        map!(parse_byte, Expression::Byte)
                    ) >>
                (Instruction::LD(vx, expr))
            )
        )
    ))
);

named!(parse_i_low<Instruction>,
    do_parse!(tag_no_case!("low") >> (Instruction::LOW))
);

named!(parse_i_or<Instruction>,
    ws!(do_parse!(
        tag_no_case!("or") >> vx: parse_vreg >> tag!(",") >> vy: parse_vreg >>
        (Instruction::OR(vx, vy))
    ))
);

named!(parse_i_ret<Instruction>,
    do_parse!(tag_no_case!("ret") >> (Instruction::RET))
);

named!(parse_i_rnd<Instruction>,
    ws!(do_parse!(
        tag_no_case!("rnd") >> vx: parse_vreg >> tag!(",") >> nn: parse_byte >>
        (Instruction::RND(vx, Expression::Byte(nn)))
    ))
);

named!(parse_i_scd<Instruction>,
    ws!(do_parse!(
        tag_no_case!("scd") >> n: parse_nibble >> (Instruction::SCD(n))
    ))
);

named!(parse_i_scl<Instruction>,
    do_parse!(tag_no_case!("scl") >> (Instruction::SCL))
);

named!(parse_i_scr<Instruction>,
    do_parse!(tag_no_case!("scr") >> (Instruction::SCR))
);

named!(parse_i_se<Instruction>,
    ws!(do_parse!(
        tag_no_case!("se") >> vx: parse_vreg >> tag!(",") >>
        expr: alt_complete!(
                parse_vreg => { Expression::Reg } |
                parse_byte => { Expression::Byte }
            ) >>
        (Instruction::SE(vx, expr))
    ))
);

named!(parse_i_shl<Instruction>,
    ws!(preceded!(
        tag_no_case!("shl"),
        alt_complete!(
            do_parse!(
                vx: parse_vreg >> tag!(",") >> vy: parse_vreg >>
                (Instruction::SHL(vx, vy))
            ) |
            map!(parse_vreg, |vx| Instruction::SHL(vx, Register::V(0)))
        )
    ))
);

named!(parse_i_shr<Instruction>,
    ws!(preceded!(
        tag_no_case!("shr"),
        alt_complete!(
            do_parse!(
                vx: parse_vreg >> tag!(",") >> vy: parse_vreg >>
                (Instruction::SHR(vx, vy))
            ) |
            map!(parse_vreg, |vx| Instruction::SHR(vx, Register::V(0)))
        )
    ))
);

named!(parse_i_skp<Instruction>,
    ws!(preceded!(
        tag_no_case!("skp"),
        map!(parse_vreg, Instruction::SKP)
    ))
);

named!(parse_i_sknp<Instruction>,
    ws!(preceded!(
        tag_no_case!("sknp"),
        map!(parse_vreg, Instruction::SKNP)
    ))
);

named!(parse_i_sne<Instruction>,
    ws!(do_parse!(
        tag_no_case!("sne") >> vx: parse_vreg >> tag!(",") >>
        expr: alt_complete!(
                parse_vreg => { Expression::Reg } |
                parse_byte => { Expression::Byte }
            ) >>
        (Instruction::SNE(vx, expr))
    ))
);

named!(parse_i_sub<Instruction>,
    ws!(do_parse!(
        tag_no_case!("sub") >> vx: parse_vreg >> tag!(",") >> vy: parse_vreg >>
        (Instruction::SUB(vx, vy))
    ))
);

named!(parse_i_subn<Instruction>,
    ws!(do_parse!(
        tag_no_case!("subn") >> vx: parse_vreg >> tag!(",") >> vy: parse_vreg >>
        (Instruction::SUBN(vx, vy))
    ))
);

named!(parse_i_sys<Instruction>,
    ws!(preceded!(
        tag_no_case!("sys"),
        map!(parse_addr, Instruction::SYS)
    ))
);

named!(parse_i_xor<Instruction>,
    ws!(do_parse!(
        tag_no_case!("xor") >> vx: parse_vreg >> tag!(",") >> vy: parse_vreg >>
        (Instruction::XOR(vx, vy))
    ))
);

named!(parse_instruction<Instruction>,
    alt_complete!(
        parse_i_add  |
        parse_i_call |
        parse_i_and  |
        parse_i_cls  |
        parse_i_drw  |
        parse_i_exit |
        parse_i_high |
        parse_i_jp   |
        parse_i_ld   |
        parse_i_low  |
        parse_i_or   |
        parse_i_ret  |
        parse_i_rnd  |
        parse_i_scd  |
        parse_i_scl  |
        parse_i_scr  |
        parse_i_se   |
        parse_i_shl  |
        parse_i_shr  |
        parse_i_skp  |
        parse_i_sknp |
        parse_i_sne  |
        parse_i_sub  |
        parse_i_subn |
        parse_i_sys  |
        parse_i_xor
    )
);


named!(parse_comment<()>,
    do_parse!(
        tag!(";") >> not_line_ending >> line_ending >>
        (())
    )
);


#[derive(Debug, PartialEq)]
pub enum Item<'a> {
    Lbl(&'a str),
    Dir(Directive),
    Ins(Instruction),
    Comment,
}


named!(parse_item<Item>,
    ws!(do_parse!(
        item: alt_complete!(
            parse_instruction => { Item::Ins } |
            parse_directive   => { Item::Dir } |
            parse_label_def   => { Item::Lbl } |
            parse_comment     => { |_| Item::Comment }
        ) >> (item)
    ))
);


named!(pub parse_program<Vec<Item>>, complete!(many1!(parse_item)));


#[cfg(test)]
mod test {
    use super::*;

    macro_rules! parse_test {
        ($test_name:ident, $parse:ident, $result:expr, $( $input:expr ),* ) => {
            #[test]
            fn $test_name() {
                $(
                    assert_eq!($parse($input), IResult::Done(&b""[..], $result));
                )*
            }
        }
    }

    parse_test!(parse_register_v0, parse_vreg, Register::V(0x0), b"v0", b"V0");
    parse_test!(parse_register_v1, parse_vreg, Register::V(0x1), b"v1", b"V1");
    parse_test!(parse_register_v2, parse_vreg, Register::V(0x2), b"v2", b"V2");
    parse_test!(parse_register_v3, parse_vreg, Register::V(0x3), b"v3", b"V3");
    parse_test!(parse_register_v4, parse_vreg, Register::V(0x4), b"v4", b"V4");
    parse_test!(parse_register_v5, parse_vreg, Register::V(0x5), b"v5", b"V5");
    parse_test!(parse_register_v6, parse_vreg, Register::V(0x6), b"v6", b"V6");
    parse_test!(parse_register_v7, parse_vreg, Register::V(0x7), b"v7", b"V7");
    parse_test!(parse_register_v8, parse_vreg, Register::V(0x8), b"v8", b"V8");
    parse_test!(parse_register_v9, parse_vreg, Register::V(0x9), b"v9", b"V9");
    parse_test!(parse_register_va, parse_vreg, Register::V(0xA), b"va", b"VA", b"vA", b"Va");
    parse_test!(parse_register_vb, parse_vreg, Register::V(0xB), b"vb", b"VB", b"vB", b"Vb");
    parse_test!(parse_register_vc, parse_vreg, Register::V(0xC), b"vc", b"VC", b"vC", b"Vc");
    parse_test!(parse_register_vd, parse_vreg, Register::V(0xD), b"vd", b"VD", b"vD", b"Vd");
    parse_test!(parse_register_ve, parse_vreg, Register::V(0xE), b"ve", b"VE", b"vE", b"Ve");
    parse_test!(parse_register_vf, parse_vreg, Register::V(0xF), b"vf", b"VF", b"vF", b"Vf");

    parse_test!(parse_add_vx_vy, parse_i_add,
                Instruction::ADD(Register::V(0x4),
                                 Expression::Reg(Register::V(0xA))),
                b"add V4, VA", b"ADD v4, VA", b"Add V4,VA", b"add \tv4 , va ");
    parse_test!(parse_call, parse_i_call,
                Instruction::CALL(Expression::Addr(0x600)),
                b"CALL 0x600", b"call\t0x600", b"Call 1536");
    parse_test!(parse_and, parse_i_and,
                Instruction::AND(Register::V(0x5), Register::V(0xE)),
                b"and v5,ve", b"AND v5,\tvE", b"and V5 , VE");
    parse_test!(parse_ld_addr, parse_i_ld,
                Instruction::LD(Register::I, Expression::Addr(0x2)),
                b"ld I, 2", b"ld I,0x2");
    parse_test!(parse_ld_b_vx, parse_i_ld,
                Instruction::LD(Register::B, Expression::Reg(Register::V(0xA))),
                b"ld b,va", b"LD B, VA");
    parse_test!(parse_ld_bracki_vx, parse_i_ld,
                Instruction::LD(Register::I, Expression::Reg(Register::V(0xE))),
                b"ld [i], ve", b"LD [ I ] , vE");
    parse_test!(parse_ld_vx_dt, parse_i_ld,
                Instruction::LD(Register::V(0x1), Expression::Reg(Register::DT)),
                b"LD V1, DT", b"ld v1,dt");
    parse_test!(parse_ld_vx_k, parse_i_ld,
                Instruction::LD(Register::V(0x1), Expression::Reg(Register::K)),
                b"LD V1, K", b"ld v1,k");
    parse_test!(parse_ld_vx_r, parse_i_ld,
                Instruction::LD(Register::V(0x1), Expression::Reg(Register::R)),
                b"LD V1, r", b"ld v1,R");
    parse_test!(parse_ld_vx_i, parse_i_ld,
                Instruction::LD(Register::V(0x1), Expression::Reg(Register::I)),
                b"LD V1, [I]", b"ld v1,[i]", b"LD v1, [ I ]");
    parse_test!(parse_se_vx_byte, parse_i_se,
                Instruction::SE(Register::V(0x4), Expression::Byte(42)),
                b"se v4, 42", b"Se V4 , 42");
    parse_test!(parse_se_vx_vy, parse_i_se,
                Instruction::SE(Register::V(0x4), Expression::Reg(Register::V(0x1))),
                b"SE V4,V1", b"Se v4, v1", b"se V4, V1");
    parse_test!(parse_shl_vx, parse_i_shl,
                Instruction::SHL(Register::V(0x4), Register::V(0)),
                b"shl v4", b"SHL V4, v0");

    parse_test!(parse_item_label, parse_item,
                Item::Lbl("foobar"),
                b"  foobar : ", b"foobar:", b"foobar  :", b"foobar:  ");

    parse_test!(parse_comment_line, parse_comment, (),
                b";\n", b"; foo bar baz\n");

    parse_test!(parse_program_1, parse_program,
                vec![Item::Comment,
                     Item::Lbl("main"),
                     Item::Ins(Instruction::RET)],
                b"; This is a comment
                  main:
                    ret
                ");

    parse_test!(parse_program_2, parse_program,
                vec![Item::Lbl("loop"),
                     Item::Ins(Instruction::JP(Expression::Void,
                                               Expression::Label(String::from("loop"))))],
                b"loop: jp loop");

    parse_test!(parse_program_3, parse_program,
                vec![Item::Dir(Directive::OPTION(AsmOption::BINARY)),
                     Item::Lbl("loop"),
                     Item::Ins(Instruction::JP(Expression::Void,
                                               Expression::Label(String::from("loop"))))],
                b"option binary

loop:
    jp loop
");
}
