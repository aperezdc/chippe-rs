//
// rng.rs
// X-ABC 8-bit random number generator
//
// Copyright (C) 2016 Adrian Perez <aperez@igalia.com>
// Distributed under terms of the MIT license.
//

#[derive(Default)]
pub struct XAbcRng {
    x: u8,
    a: u8,
    b: u8,
    c: u8,
}

impl XAbcRng {
    pub fn new() -> Self {
        XAbcRng { ..Default::default() }
    }

    pub fn seed(&mut self, c: u8) {
        self.x = c;
        self.a = c;
        self.b = c;
        self.c = c;
    }

    pub fn last(&self) -> u8 {
        self.c
    }

    pub fn next(&mut self) -> u8  {
        self.x += 51;
        self.a ^= self.c ^ self.x;
        self.b += self.a;
        self.c += (self.b >> 1) ^ self.a;
        self.c
    }
}
