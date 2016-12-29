Chippe-RS
=========

This is set of [CHIP-8](https://en.wikipedia.org/wiki/CHIP-8)-related tools
written in [Rust](https://www.rust-lang.org/).

Note that this is a **toy project of mine used as playground to learn Rust**,
so the quality of the code may be variable. Also, the focus is to produce
*correct* implementations of the tools, without aiming for performance.

Implemented so far:

* Assembler. The source syntax is a superset of the syntax used with the
  [Chipper](http://www.hpcalc.org/details/6735) assembler.

* CPU emulation module ([chip8.rs](src/chip8.rs)).

Planned:

* Emulator using SDL for display, sound, and input handling.

* Disassembler.


License
-------

The source code is distributed under the terms of the [GPL3
license](https://www.gnu.org/licenses/gpl-3.0.en.html)

