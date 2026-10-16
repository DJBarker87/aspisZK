    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct Challenges {
        pub lambda: QM31,
        pub chi: QM31,
        pub theta: QM31,
        pub zc: [QM31; 10],
        pub mu: QM31,
        pub eta: QM31,
    }