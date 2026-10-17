    #[derive(Clone, Copy)]
    pub enum Column<'a> {
        Base(&'a [M31; 1024]),
        Extension(&'a [QM31; 1024]),
    }