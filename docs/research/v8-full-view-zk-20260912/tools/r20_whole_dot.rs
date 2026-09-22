//! Source-local whole-dot candidate over the actual Aspis QM31 representation.
//!
//! This module is an arithmetic candidate only.  `dot` performs one boundary
//! canonicality check, then `Dot::push` may assume canonical QM31 limbs.  The
//! accumulator retains the packet's nine channels, four-product u64 chunks,
//! 4096-term bound, and one final QM31 reconstruction.
use aspis_core::field::{CM31, M31, P, QM31};

pub const MAX_TERMS: usize = 4096;

#[derive(Clone, Copy, Debug)]
pub struct TooLong;

#[derive(Clone, Copy, Debug)]
pub enum Error {
    Length,
    NonCanonical,
    TooLong,
}

#[inline(always)]
fn canonical(x: QM31) -> bool {
    x.c0.a.0 < P && x.c0.b.0 < P && x.c1.a.0 < P && x.c1.b.0 < P
}

#[inline(always)]
fn channels(x: QM31) -> [u32; 9] {
    let a = x.c0.a;
    let b = x.c0.b;
    let c = x.c1.a;
    let d = x.c1.b;
    let x0 = a.add(c);
    let x1 = b.add(d);
    [
        a.0,
        b.0,
        a.add(b).0,
        c.0,
        d.0,
        c.add(d).0,
        x0.0,
        x1.0,
        x0.add(x1).0,
    ]
}

#[inline(always)]
fn mul_by_r(x: CM31) -> CM31 {
    CM31 {
        a: x.a.double().sub(x.b),
        b: x.a.add(x.b.double()),
    }
}

#[inline(always)]
fn reconstruct(r: [M31; 9]) -> QM31 {
    let part = |j: usize| {
        let m0 = r[j].sub(r[j + 1]);
        let m1 = r[j + 2].sub(r[j]).sub(r[j + 1]);
        (m0, m1)
    };
    let (a0, b0) = part(0);
    let (a1, b1) = part(3);
    let (a2, b2) = part(6);
    let c0 = CM31 { a: a0, b: b0 };
    let c1 = CM31 { a: a1, b: b1 };
    let c2 = CM31 { a: a2, b: b2 };
    QM31 {
        c0: c0.add(mul_by_r(c1)),
        c1: c2.sub(c0).sub(c1),
    }
}

#[derive(Clone, Copy)]
pub struct Dot {
    raw: [u64; 9],
    total: [u64; 9],
    pending: u8,
    count: usize,
}

impl Dot {
    pub const fn new() -> Self {
        Self {
            raw: [0; 9],
            total: [0; 9],
            pending: 0,
            count: 0,
        }
    }

    #[inline(always)]
    fn flush(&mut self) {
        for j in 0..9 {
            let part = (self.raw[j] & u64::from(P)) + (self.raw[j] >> 31);
            self.total[j] = self.total[j].wrapping_add(part);
            self.raw[j] = 0;
        }
        self.pending = 0;
    }

    /// Push canonical operands after the caller has checked every input limb.
    /// This is crate-visible so source-local adapters cannot turn it into a
    /// public field API or silently admit arbitrary QM31 constructors.
    #[inline(always)]
    pub(crate) fn push_canonical(&mut self, left: QM31, right: QM31) -> Result<(), TooLong> {
        if self.count == MAX_TERMS {
            return Err(TooLong);
        }
        if self.pending == 4 {
            self.flush();
        }
        let a = channels(left);
        let b = channels(right);
        for j in 0..9 {
            self.raw[j] = self.raw[j].wrapping_add(u64::from(a[j]) * u64::from(b[j]));
        }
        self.count += 1;
        self.pending += 1;
        Ok(())
    }

    #[inline(always)]
    pub fn finish(mut self) -> QM31 {
        if self.count == 0 {
            return QM31::ZERO;
        }
        if self.count <= 4 {
            return reconstruct(self.raw.map(M31::reduce_u64));
        }
        if self.pending != 0 {
            self.flush();
        }
        reconstruct(self.total.map(M31::reduce_u64))
    }
}

pub fn dot(left: &[QM31], right: &[QM31]) -> Result<QM31, Error> {
    if left.len() != right.len() {
        return Err(Error::Length);
    }
    if left.len() > MAX_TERMS {
        return Err(Error::TooLong);
    }
    if left.iter().chain(right.iter()).any(|&x| !canonical(x)) {
        return Err(Error::NonCanonical);
    }
    let mut out = Dot::new();
    for (&a, &b) in left.iter().zip(right.iter()) {
        out.push_canonical(a, b).map_err(|_| Error::TooLong)?;
    }
    Ok(out.finish())
}
