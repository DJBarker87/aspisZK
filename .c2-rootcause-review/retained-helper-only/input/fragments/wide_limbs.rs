    #[inline(always)]
    pub const fn to_limbs(self) -> [u32; Self::LIMB_COUNT] {
        [
            self.c0.c0.a.0,
            self.c0.c0.b.0,
            self.c0.c1.a.0,
            self.c0.c1.b.0,
            self.c1.c0.a.0,
            self.c1.c0.b.0,
            self.c1.c1.a.0,
            self.c1.c1.b.0,
        ]
    }