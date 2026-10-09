//! The R0 wide field, independently of transcript sampling or proof encoding.

use super::{CM31, M31, P, QM31};

/// `E = QM31[v]/(v² - u)`, where `u² = 2+i` and `i² = -1`.
///
/// Exactly two QM31 coordinates, `c0 + c1*v`, or eight canonical M31 limbs.
/// For digits `d[0..8]` in `[0, P)`, the exact decode formula is
///
/// ```text
/// decode4(a,b,c,d) = (a + b*i) + (c + d*i)*u
/// decode8(d) = decode4(d0,d1,d2,d3) + decode4(d4,d5,d6,d7)*v
/// ```
///
/// Thus limb order is `(c0.c0.a, c0.c0.b, c0.c1.a, c0.c1.b,
/// c1.c0.a, c1.c0.b, c1.c1.a, c1.c1.b)`, matching
/// `R0C/ModuloField.lean:digitsField_apply` (lines 38–40) and
/// `AspisV8R19/SamplerFieldDecode.lean:decode4` (line 10).
/// `WideTower.lean:qm31_wideU_not_isSquare` supplies the mathematical
/// non-residue fact; `wideExact_card` gives `|E| = P^8`.
/// These references specify the arithmetic; they do not prove this Rust code.
///
/// Coordinates are private to preserve canonicality. Algebraic constructors
/// reduce raw QM31 representatives; wire/digit decoders reject noncanonical
/// input. All operations are total except inversion, which returns `None` at
/// zero. This reference implementation makes no constant-time claim.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct WideExact {
    c0: QM31,
    c1: QM31,
}

impl WideExact {
    pub const LIMB_COUNT: usize = 8;
    pub const BYTE_LEN: usize = 32;
    /// The QM31 generator, not `2+i`: `U = (0,1)` in QM31 coordinates.
    pub const U: QM31 = QM31 {
        c0: CM31::ZERO,
        c1: CM31::ONE,
    };
    pub const ZERO: Self = Self {
        c0: QM31::ZERO,
        c1: QM31::ZERO,
    };
    pub const ONE: Self = Self {
        c0: QM31::ONE,
        c1: QM31::ZERO,
    };
    pub const V: Self = Self {
        c0: QM31::ZERO,
        c1: QM31::ONE,
    };

    /// Construct `c0 + c1*v`, reducing each raw M31 representative modulo P.
    pub fn new(c0: QM31, c1: QM31) -> Self {
        Self {
            c0: canonical_qm31(c0),
            c1: canonical_qm31(c1),
        }
    }

    pub const fn c0(self) -> QM31 {
        self.c0
    }
    pub const fn c1(self) -> QM31 {
        self.c1
    }

    /// The field embedding `x -> x + 0*v`; canonicalizes raw QM31 limbs.
    pub fn from_qm31(value: QM31) -> Self {
        Self {
            c0: canonical_qm31(value),
            c1: QM31::ZERO,
        }
    }

    pub fn add(self, rhs: Self) -> Self {
        #[cfg(feature = "r0-op-count")]
        let _count = crate::r0_op_count::enter(crate::r0_op_count::Op::EAdd);
        Self {
            c0: self.c0.add(rhs.c0),
            c1: self.c1.add(rhs.c1),
        }
    }

    pub fn sub(self, rhs: Self) -> Self {
        #[cfg(feature = "r0-op-count")]
        let _count = crate::r0_op_count::enter(crate::r0_op_count::Op::ESub);
        Self {
            c0: self.c0.sub(rhs.c0),
            c1: self.c1.sub(rhs.c1),
        }
    }

    pub fn neg(self) -> Self {
        #[cfg(feature = "r0-op-count")]
        let _count = crate::r0_op_count::enter(crate::r0_op_count::Op::ENeg);
        Self {
            c0: self.c0.neg(),
            c1: self.c1.neg(),
        }
    }

    /// `(a+b*v)(c+d*v) = (ac+u*bd) + (ad+bc)*v`.
    pub fn mul(self, rhs: Self) -> Self {
        #[cfg(feature = "r0-op-count")]
        let _count = crate::r0_op_count::enter(crate::r0_op_count::Op::EMul);
        #[cfg(all(feature = "r0-probe-reference", not(target_os = "solana")))]
        if crate::r0_probe::equality_trace::is_reference() {
            return self.mul_re3(rhs);
        }
        #[cfg(feature = "r0-cost-probe")]
        {
            let ac = self.c0.mul(rhs.c0);
            let bd = self.c1.mul(rhs.c1);
            let cross = self.c0.add(self.c1).mul(rhs.c0.add(rhs.c1));
            Self {
                c0: ac.add(mul_u(bd)),
                c1: cross.sub(ac).sub(bd),
            }
        }
        #[cfg(not(feature = "r0-cost-probe"))]
        {
            self.mul_re3(rhs)
        }
    }
    /// Schoolbook outer layer retained for default builds and equality gates.
    pub fn mul_re3(self, rhs: Self) -> Self {
        Self {
            c0: self.c0.mul(rhs.c0).add(mul_u(self.c1.mul(rhs.c1))),
            c1: self.c0.mul(rhs.c1).add(self.c1.mul(rhs.c0)),
        }
    }

    /// `(a+b*v)^2 = (a^2+u*b^2) + (2ab)*v`.
    pub fn square(self) -> Self {
        #[cfg(feature = "r0-op-count")]
        let _count = crate::r0_op_count::enter(crate::r0_op_count::Op::ESquare);
        let cross = self.c0.mul(self.c1);
        Self {
            c0: self.c0.square().add(mul_u(self.c1.square())),
            c1: cross.add(cross),
        }
    }

    /// `(a+b*v)^-1 = (a-b*v)/(a^2-u*b^2)`. Returns `None` at zero.
    /// Since u is a nonsquare in QM31, the norm is nonzero for nonzero self.
    pub fn try_inv(self) -> Option<Self> {
        #[cfg(feature = "r0-op-count")]
        let _count = crate::r0_op_count::enter(crate::r0_op_count::Op::EInv);
        let norm = self.c0.square().sub(mul_u(self.c1.square()));
        let inverse_norm = norm.try_inv()?;
        Some(Self {
            c0: self.c0.mul(inverse_norm),
            c1: self.c1.neg().mul(inverse_norm),
        })
    }

    /// Binary exponentiation, with `0^0 = 1`, as for the existing tower.
    pub fn pow(self, mut exponent: u64) -> Self {
        let mut result = Self::ONE;
        let mut base = self;
        while exponent != 0 {
            if exponent & 1 != 0 {
                result = result.mul(base);
            }
            base = base.square();
            exponent >>= 1;
        }
        result
    }

    /// Mixed multiplication `(a+b*v)*r = ar + br*v`, for `r` in QM31.
    pub fn mul_qm31(self, rhs: QM31) -> Self {
        #[cfg(feature = "r0-op-count")]
        let _count = crate::r0_op_count::enter(crate::r0_op_count::Op::EMulK);
        let rhs = canonical_qm31(rhs);
        Self {
            c0: self.c0.mul(rhs),
            c1: self.c1.mul(rhs),
        }
    }

    /// Scalar multiplication without lifting to a full E product.
    pub fn mul_m31(self, rhs: M31) -> Self {
        #[cfg(feature = "r0-op-count")]
        let _count = crate::r0_op_count::enter(crate::r0_op_count::Op::EMulF);
        let rhs = M31(rhs.0 % P);
        Self {
            c0: self.c0.mul_m31(rhs),
            c1: self.c1.mul_m31(rhs),
        }
    }

    pub fn is_zero(self) -> bool {
        self.c0.is_zero() && self.c1.is_zero()
    }

    /// Decode eight base-P digits without reduction; rejects any digit >= P.
    /// This is `digitsField`, not the natural-number cast of a base-P rank.
    pub fn from_limbs(limbs: [u32; Self::LIMB_COUNT]) -> Option<Self> {
        if limbs.iter().any(|&limb| limb >= P) {
            return None;
        }
        let [a, b, c, d, e, f, g, h] = limbs;
        Some(Self {
            c0: QM31 {
                c0: CM31 {
                    a: M31(a),
                    b: M31(b),
                },
                c1: CM31 {
                    a: M31(c),
                    b: M31(d),
                },
            },
            c1: QM31 {
                c0: CM31 {
                    a: M31(e),
                    b: M31(f),
                },
                c1: CM31 {
                    a: M31(g),
                    b: M31(h),
                },
            },
        })
    }

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

    /// Exactly 32 bytes: eight little-endian u32 limbs in `digitsField` order.
    /// Rejects both wrong lengths and noncanonical limbs, without slicing an
    /// unvalidated input. This is a field encoding, not the R-B block sampler.
    pub fn from_le_bytes(bytes: &[u8]) -> Option<Self> {
        let bytes: &[u8; Self::BYTE_LEN] = bytes.try_into().ok()?;
        let mut limbs = [0; Self::LIMB_COUNT];
        for (limb, chunk) in limbs.iter_mut().zip(bytes.chunks_exact(4)) {
            *limb = u32::from_le_bytes(chunk.try_into().ok()?);
        }
        Self::from_limbs(limbs)
    }

    pub fn to_le_bytes(self) -> [u8; Self::BYTE_LEN] {
        let mut bytes = [0; Self::BYTE_LEN];
        for (chunk, limb) in bytes.chunks_exact_mut(4).zip(self.to_limbs()) {
            chunk.copy_from_slice(&limb.to_le_bytes());
        }
        bytes
    }
}

fn canonical_qm31(value: QM31) -> QM31 {
    let reduce = |x: M31| M31(x.0 % P);
    QM31 {
        c0: CM31 {
            a: reduce(value.c0.a),
            b: reduce(value.c0.b),
        },
        c1: CM31 {
            a: reduce(value.c1.a),
            b: reduce(value.c1.b),
        },
    }
}

/// `u*(a+b*u) = (2+i)*b + a*u`.
fn mul_u(value: QM31) -> QM31 {
    QM31 {
        c0: super::mul_by_r(value.c1),
        c1: value.c0,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn next(state: &mut u64) -> WideExact {
        WideExact::from_limbs(core::array::from_fn(|_| {
            *state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            (*state % u64::from(P)) as u32
        }))
        .unwrap()
    }

    fn basis(index: usize) -> WideExact {
        let mut limbs = [0; 8];
        limbs[index] = 1;
        WideExact::from_limbs(limbs).unwrap()
    }

    fn assert_canonical(x: WideExact) {
        assert!(x.to_limbs().iter().all(|&d| d < P));
    }

    // Independent schoolbook polynomial oracle over integer coefficients.
    // No M31/CM31/QM31 arithmetic: reduce v^2=u, u^2=2+i, i^2=-1,
    // then reduce signed integer coefficients modulo P.
    fn polynomial_product(a: [u32; 8], b: [u32; 8]) -> [u32; 8] {
        let mut coefficients = [0i128; 8];
        for (j, a) in a.into_iter().enumerate() {
            for (k, b) in b.into_iter().enumerate() {
                let i = (j & 1) + (k & 1);
                let v = (j >> 2) + (k >> 2);
                let u = ((j >> 1) & 1) + ((k >> 1) & 1) + v / 2;
                let mut term = |i: usize, scale: i128| {
                    let index = (i % 2) + 2 * (u % 2) + 4 * (v % 2);
                    let sign = if i / 2 % 2 == 0 { 1 } else { -1 };
                    coefficients[index] += sign * scale * i128::from(a) * i128::from(b);
                };
                if u >= 2 {
                    term(i, 2);
                    term(i + 1, 1);
                } else {
                    term(i, 1);
                }
            }
        }
        coefficients.map(|c| c.rem_euclid(i128::from(P)) as u32)
    }

    #[test]
    fn wide_exact_hand_computed_products() {
        let one = WideExact::ONE;
        let i = basis(1);
        let u = basis(2);
        let v = WideExact::V;
        assert_eq!(v, basis(4));
        assert_eq!(WideExact::from_qm31(WideExact::U), u);
        assert_eq!(WideExact::default(), WideExact::ZERO);
        assert_eq!(v.square(), u);
        assert_eq!(u.square().to_limbs(), [2, 1, 0, 0, 0, 0, 0, 0]);
        assert_eq!(i.square(), one.neg());
        // (1+v)(1-v) = 1-u; (u+v)(u-v) = 2+i-u.
        assert_eq!(
            one.add(v).mul(one.sub(v)).to_limbs(),
            [1, 0, P - 1, 0, 0, 0, 0, 0]
        );
        assert_eq!(
            u.add(v).mul(u.sub(v)).to_limbs(),
            [2, 1, P - 1, 0, 0, 0, 0, 0]
        );
        // (iv)(uv) = i*u*v^2 = i*(2+i) = -1+2i.
        assert_eq!(
            basis(5).mul(basis(6)).to_limbs(),
            [P - 1, 2, 0, 0, 0, 0, 0, 0]
        );
        // (1+i+u+v)^2 = (2+3i)+(3+2i)u+(2+2i+2u)v.
        assert_eq!(
            one.add(i).add(u).add(v).square().to_limbs(),
            [2, 3, 3, 2, 2, 2, 2, 0]
        );
        // Dense hand calculation, with a,b the low/high coordinates of x,
        // and c,d those of y:
        // ac=(-49+99i)+(-8+70i)u; bd=(-9+91i)+(8+70i)u;
        // ad=(-9+35i)+30iu; bc=(-81+251i)+174iu.
        // ac+u*bd=(-103+247i)+(-17+161i)u; ad+bc=(-90+286i)+204iu.
        let x = WideExact::from_limbs([1, 2, 3, 4, 5, 6, 7, 8]).unwrap();
        let y = WideExact::from_limbs([8, 7, 6, 5, 4, 3, 2, 1]).unwrap();
        assert_eq!(
            x.mul(y).to_limbs(),
            [P - 103, 247, P - 17, 161, P - 90, 286, 0, 204]
        );
        // v^-1 = ((2-i)/5)*u*v, with 1/5 = 858993459 mod P.
        assert_eq!(
            v.try_inv().unwrap().to_limbs(),
            [0, 0, 0, 0, 0, 0, 1717986918, 1288490188]
        );
    }

    #[test]
    fn wide_exact_products_match_independent_polynomial_oracle() {
        for j in 0..8 {
            for k in 0..8 {
                let a = basis(j);
                let b = basis(k);
                assert_eq!(
                    a.mul(b).to_limbs(),
                    polynomial_product(a.to_limbs(), b.to_limbs())
                );
            }
        }
        let mut state = 0x5749_4445_5241_0001;
        for _ in 0..1024 {
            let a = next(&mut state);
            let b = next(&mut state);
            assert_eq!(
                a.mul(b).to_limbs(),
                polynomial_product(a.to_limbs(), b.to_limbs())
            );
        }
        let high = WideExact::from_limbs([P - 1; 8]).unwrap();
        assert_eq!(
            high.square().to_limbs(),
            polynomial_product([P - 1; 8], [P - 1; 8])
        );
    }

    #[test]
    fn wide_exact_random_ring_laws_and_canonical_outputs() {
        let mut state = 0x5749_4445_5241_0002;
        for _ in 0..4096 {
            let a = next(&mut state);
            let b = next(&mut state);
            let c = next(&mut state);
            assert_eq!(a.add(b), b.add(a));
            assert_eq!(a.add(b).add(c), a.add(b.add(c)));
            assert_eq!(a.mul(b), b.mul(a));
            assert_eq!(a.mul(b).mul(c), a.mul(b.mul(c)));
            assert_eq!(a.mul(b.add(c)), a.mul(b).add(a.mul(c)));
            assert_eq!(a.add(WideExact::ZERO), a);
            assert_eq!(a.mul(WideExact::ONE), a);
            assert_eq!(a.mul(WideExact::ZERO), WideExact::ZERO);
            assert_eq!(a.add(a.neg()), WideExact::ZERO);
            assert_eq!(a.sub(b), a.add(b.neg()));
            assert_eq!(a.add(b).sub(b), a);
            assert_eq!(a.neg().neg(), a);
            assert_eq!(a.square(), a.mul(a));
            for x in [a.add(b), a.sub(b), a.neg(), a.mul(b), a.square()] {
                assert_canonical(x);
            }
        }
    }

    #[test]
    fn wide_exact_inverse_roundtrips_including_edges() {
        assert_eq!(WideExact::ZERO.try_inv(), None);
        let mut state = 0x5749_4445_5241_0003;
        for a in (0..8)
            .map(basis)
            .chain([
                WideExact::ONE.neg(),
                WideExact::from_limbs([P - 1; 8]).unwrap(),
            ])
            .chain((0..1024).map(|_| next(&mut state)))
        {
            let inverse = a.try_inv().unwrap();
            assert_eq!(a.mul(inverse), WideExact::ONE);
            assert_eq!(inverse.mul(a), WideExact::ONE);
            assert_eq!(inverse.try_inv(), Some(a));
            assert_canonical(inverse);
        }
    }

    #[test]
    fn wide_exact_pow_and_qm31_embedding() {
        assert_eq!(WideExact::ZERO.pow(0), WideExact::ONE);
        assert_eq!(WideExact::ZERO.pow(1), WideExact::ZERO);
        let mut state = 0x5749_4445_5241_0004;
        for _ in 0..128 {
            let a = next(&mut state);
            let b = next(&mut state);
            let x = WideExact::from_qm31(a.c0());
            let y = WideExact::from_qm31(b.c0());
            assert_eq!(x.c0(), a.c0());
            assert_eq!(x.c1(), QM31::ZERO);
            assert_eq!(x.mul(y), WideExact::from_qm31(a.c0().mul(b.c0())));
            assert_eq!(x.add(y), WideExact::from_qm31(a.c0().add(b.c0())));
            assert_eq!(a.mul_qm31(b.c0()), a.mul(y));
            assert_eq!(a.mul_qm31(QM31::ZERO), WideExact::ZERO);
            assert_eq!(a.mul_qm31(QM31::ONE), a);
            let mut repeated = WideExact::ONE;
            for exponent in 0..32 {
                assert_eq!(a.pow(exponent), repeated);
                repeated = repeated.mul(a);
            }
            assert_eq!(a.pow(u64::MAX), a.pow(u64::MAX - 1).mul(a));
            // |E|=P^8: eight P-power Frobenius applications fix each element.
            let mut frobenius = a;
            for _ in 0..8 {
                frobenius = frobenius.pow(u64::from(P));
            }
            assert_eq!(frobenius, a);
        }
    }

    #[test]
    fn wide_exact_u_is_not_a_sampled_qm31_square() {
        // Reference fact: WideTower.lean:qm31_wideU_not_isSquare.
        // Sampling is a regression check, not a replacement for that proof.
        let mut state = 0x5749_4445_5241_0005;
        for x in [QM31::ZERO, QM31::ONE, WideExact::U]
            .into_iter()
            .chain((0..4096).map(|_| next(&mut state).c0()))
        {
            assert_ne!(x.square(), WideExact::U);
        }
        // Euler criterion, independently pinning u rather than another non-residue.
        let mut exponent = (u128::from(P).pow(4) - 1) / 2;
        let mut base = WideExact::U;
        let mut result = QM31::ONE;
        while exponent != 0 {
            if exponent & 1 != 0 {
                result = result.mul(base);
            }
            base = base.square();
            exponent >>= 1;
        }
        assert_eq!(result, QM31::ONE.neg());
        let mut v = WideExact::V;
        for _ in 0..4 {
            v = v.pow(u64::from(P));
        }
        assert_eq!(v, WideExact::V.neg()); // v is outside the QM31 subfield.
    }

    #[test]
    fn wide_exact_canonical_digits_and_bytes_roundtrip() {
        assert_eq!(WideExact::LIMB_COUNT, 8);
        assert_eq!(core::mem::size_of::<WideExact>(), 32);
        let mut state = 0x5749_4445_5241_0006;
        for x in [
            WideExact::ZERO,
            WideExact::ONE,
            WideExact::from_limbs([P - 1; 8]).unwrap(),
        ]
        .into_iter()
        .chain((0..1024).map(|_| next(&mut state)))
        {
            assert_eq!(WideExact::from_limbs(x.to_limbs()), Some(x));
            assert_eq!(WideExact::from_le_bytes(&x.to_le_bytes()), Some(x));
        }
        // Explicit byte/lane ordering, independently of the round-trip.
        let limbs = [1, 2, 3, 4, 5, 6, 7, 8];
        let x = WideExact::from_limbs(limbs).unwrap();
        assert_eq!(
            x.c0(),
            QM31 {
                c0: CM31::new(M31(1), M31(2)),
                c1: CM31::new(M31(3), M31(4))
            }
        );
        assert_eq!(
            x.c1(),
            QM31 {
                c0: CM31::new(M31(5), M31(6)),
                c1: CM31::new(M31(7), M31(8))
            }
        );
        assert_eq!(
            x.to_le_bytes(),
            [
                1, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 5, 0, 0, 0, 6, 0, 0, 0, 7, 0, 0, 0,
                8, 0, 0, 0
            ]
        );
        let x = WideExact::from_limbs([0x12345678; 8]).unwrap();
        assert!(x
            .to_le_bytes()
            .chunks_exact(4)
            .all(|b| b == [0x78, 0x56, 0x34, 0x12]));
    }

    #[test]
    fn wide_exact_rejects_malformed_encodings_without_panics() {
        let bytes = [0u8; 65];
        for len in 0..=65 {
            assert_eq!(
                WideExact::from_le_bytes(&bytes[..len]),
                if len == 32 {
                    Some(WideExact::ZERO)
                } else {
                    None
                }
            );
        }
        for index in 0..8 {
            for invalid in [P, P + 1, u32::MAX] {
                let mut limbs = [0; 8];
                limbs[index] = invalid;
                assert_eq!(WideExact::from_limbs(limbs), None);
                let mut bytes = [0; 32];
                bytes[4 * index..4 * index + 4].copy_from_slice(&invalid.to_le_bytes());
                assert_eq!(WideExact::from_le_bytes(&bytes), None);
            }
        }
    }

    #[test]
    fn wide_exact_algebraic_constructors_canonicalize_raw_qm31() {
        let raw = QM31 {
            c0: CM31::new(M31(P), M31(P + 1)),
            c1: CM31::new(M31(u32::MAX), M31(P - 1)),
        };
        let x = WideExact::new(raw, raw);
        assert_eq!(x.to_limbs(), [0, 1, 1, P - 1, 0, 1, 1, P - 1]);
        let embedded = WideExact::from_qm31(raw);
        assert_eq!(embedded.to_limbs(), [0, 1, 1, P - 1, 0, 0, 0, 0]);
        assert_eq!(x.mul_qm31(raw), x.mul(embedded));
        assert_eq!(x.mul(x.try_inv().unwrap()), WideExact::ONE);
        assert_canonical(x.add(x));
        assert_canonical(x.sub(x.neg()));
    }
}
