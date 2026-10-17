    /// Backend errors cause an abort, never a retry or a challenge filter.
    pub trait Commitments {
        fn c1(&mut self, columns: [Column<'_>; 27]) -> Result<[u8; 32], Error>;
        fn c2(&mut self, columns: [&[QM31; 1024]; 2]) -> Result<[u8; 32], Error>;
    }