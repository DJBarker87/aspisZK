    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum Error {
        Allocation,
        RowOrder { expected: u8, actual: u8 },
        InvalidRow,
        Tag { row: u8 },
        Length { row: u8 },
        NonCanonical { row: u8, value: usize },
        Boundary { round: usize },
        Terminal,
        EqualCirclePoints,
        TrailingBytes,
        Public,
    }