    #[inline(always)]
    pub fn double(self) -> M31 {
        self.add(self)
    }