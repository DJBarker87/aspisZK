// Exact source-cut: fast_pairing.rs canonical::Dot fields/new and EbyKDot fields/new.
pub mod fast_pairing {
    mod canonical {
        pub struct Dot { sums:[u64;4] }
        impl Dot {
            pub fn new()->Self {Self{sums:[0;4]}}
        }
    }
    pub struct EbyKDot {
        c0: canonical::Dot,
        c1: canonical::Dot,
        count: usize,
    }
    impl EbyKDot {
        pub fn new() -> Self {
            Self { c0: canonical::Dot::new(), c1: canonical::Dot::new(), count: 0 }
        }
    }
}

pub fn new_entry() -> fast_pairing::EbyKDot { fast_pairing::EbyKDot::new() }
