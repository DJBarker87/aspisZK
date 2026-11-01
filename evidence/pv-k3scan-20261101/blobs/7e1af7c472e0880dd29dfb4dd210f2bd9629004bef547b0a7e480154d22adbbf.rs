//! Safe P6 fallback for the current canonicalizing WideExact constructor.
//! The parent crate is cfg(kani)-only; no source correspondence is assumed.
use aspis_core::field::{ct, CM31, M31, QM31};

#[derive(Clone, Copy)]
pub struct CanonicalWide {
    pub c0: QM31,
    pub c1: QM31,
}

pub fn canonical_qm31(x: QM31) -> QM31 {
    QM31 {
        c0: CM31 {
            a: M31(ct::reduce64(x.c0.a.0 as u64)),
            b: M31(ct::reduce64(x.c0.b.0 as u64)),
        },
        c1: CM31 {
            a: M31(ct::reduce64(x.c1.a.0 as u64)),
            b: M31(ct::reduce64(x.c1.b.0 as u64)),
        },
    }
}

pub fn new(c0: QM31, c1: QM31) -> CanonicalWide {
    CanonicalWide { c0: canonical_qm31(c0), c1: canonical_qm31(c1) }
}
