//! SPEC §6. The compact view uses two roots and authenticated opened values.
use super::{
    basis::NaturalBasis,
    chord::{self, FunctionalWeights, Secant},
    domain::Point,
    transport::COEFFICIENT_TO_ROW,
    Error, Message,
};
use crate::field::WideExact as E;

pub const LANES: usize = 29;
pub type Claims = [[E; LANES]; 3];
pub type Points = [[E; 10]; 3];
pub type Endpoints = [[E; 2]; LANES];
pub type Roots = [[u8; 32]; 2];
pub const COPY_ACTIVE_ROW_MASKS: [u16; 64] = [
    6144, 6144, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145,
    6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6144, 4097, 2048, 6145, 2049, 2048, 6145,
    2049, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145,
    6145, 6145, 6145, 6145, 6145, 4097, 6145, 6145, 4097, 26214, 26214, 26214, 26214, 26214, 26214,
    1749,
];
pub fn inactive(r: usize) -> Result<bool, Error> {
    if r >= 1024 {
        return Err(Error::IndexOutOfRange);
    }
    Ok((COPY_ACTIVE_ROW_MASKS[r / 16] >> (r % 16)) & 1 == 0)
}
/// D13's inactive indicator in coefficient space: 1_I(π⁻¹(j)).
pub fn indicator() -> Message<E> {
    core::array::from_fn(|j| {
        let r = usize::from(COEFFICIENT_TO_ROW[j]);
        if (COPY_ACTIVE_ROW_MASKS[r / 16] >> (r % 16)) & 1 == 0 {
            E::ONE
        } else {
            E::ZERO
        }
    })
}
/// SPEC §6: A is MSB-first; points are LSB-first. xor12 flips bits 2,3.
pub fn points_from_alphas(a: &[E; 10]) -> Points {
    let p0 = core::array::from_fn(|b| a[9 - b]);
    let mut carry = E::ONE;
    let p1 = core::array::from_fn(|b| {
        let x = p0[b];
        let value = x.add(carry).sub(x.mul(carry).add(x.mul(carry)));
        carry = carry.mul(x);
        value
    });
    let p2 = core::array::from_fn(|b| {
        if b == 2 || b == 3 {
            E::ONE.sub(p0[b])
        } else {
            p0[b]
        }
    });
    [p0, p1, p2]
}
/// Semantic multilinear weights remain indexed by rows.
pub fn row_eq_weight(p: &[E; 10]) -> Message<E> {
    core::array::from_fn(|r| {
        (0..10).fold(E::ONE, |v, b| {
            v.mul(if (r >> b) & 1 == 0 {
                E::ONE.sub(p[b])
            } else {
                p[b]
            })
        })
    })
}
/// D13: eq(p, π⁻¹(j)), paired with t ∘ π⁻¹ throughout the opening layer.
pub fn eq_weight(p: &[E; 10]) -> Message<E> {
    super::transport::to_coefficients(&row_eq_weight(p))
}
pub fn dot<const N: usize>(a: &[E; N], b: &[E; N]) -> E {
    a.iter().zip(b).fold(E::ZERO, |v, (&x, &y)| v.add(x.mul(y)))
}
pub fn powers<const N: usize>(x: E) -> [E; N] {
    let mut p = E::ONE;
    core::array::from_fn(|_| {
        let v = p;
        p = p.mul(x);
        v
    })
}
#[derive(Clone, Debug)]
pub struct OpeningData {
    pub roots: Roots,
    pub z: [Point<E>; 2],
    pub y: Endpoints,
    pub points: Points,
    pub claims: Claims,
    // The inactive set is fixed by COPY_ACTIVE_ROW_MASKS, never proof supplied.
}
impl OpeningData {
    pub fn line(&self) -> Secant<E> {
        Secant::from_points(self.z[0], self.z[1])
    }
    pub fn validate_points(&self) -> Result<(), Error> {
        if self.z[0] == self.z[1]
            || self.z.iter().any(|z| {
                !z.is_on_circle()
                    || (z.x.to_limbs()[1..].iter().all(|&v| v == 0)
                        && z.y.to_limbs()[1..].iter().all(|&v| v == 0))
            })
        {
            return Err(Error::InvalidPoints);
        }
        Ok(())
    }
    pub fn weights(&self, kappa: E) -> Message<E> {
        let eq = self.points.map(|p| eq_weight(&p));
        let k = powers::<4>(kappa);
        let i = indicator();
        core::array::from_fn(|r| {
            i[r].add(k[1].mul(eq[0][r]))
                .add(k[2].mul(eq[1][r]))
                .add(k[3].mul(eq[2][r]))
        })
    }
    pub fn claim(&self, gamma: E, v: E, kappa: E) -> E {
        let g = powers::<29>(gamma);
        let k = powers::<4>(kappa);
        (0..3).fold(v, |sum, j| sum.add(k[j + 1].mul(dot(&g, &self.claims[j]))))
    }
    pub fn interpolant_batch(&self, gamma: E) -> Result<Message<E>, Error> {
        let g = powers::<29>(gamma);
        let y =
            core::array::from_fn(|j| (0..29).fold(E::ZERO, |s, l| s.add(g[l].mul(self.y[l][j]))));
        chord::interpolant(self.z[0], self.z[1], y)
    }
    pub fn claim_prime(&self, gamma: E, v: E, kappa: E) -> Result<E, Error> {
        Ok(self
            .claim(gamma, v, kappa)
            .sub(dot(&self.weights(kappa), &self.interpolant_batch(gamma)?)))
    }
    pub fn q_weights(&self, basis: &NaturalBasis, kappa: E) -> Result<Message<E>, Error> {
        chord::quotient_weights(basis, self.line(), &self.weights(kappa))
    }
    pub fn total_weights(
        &self,
        basis: &NaturalBasis,
        kappa: E,
        tau: E,
    ) -> Result<Message<E>, Error> {
        let qw = self.q_weights(basis, kappa)?;
        let e1 = FunctionalWeights::e1(basis)?;
        let e2 = FunctionalWeights::e2(basis, self.line().b, self.line().c)?;
        Ok(core::array::from_fn(|r| {
            qw[r].add(tau.mul(e1[r])).add(tau.mul(tau).mul(e2[r]))
        }))
    }
}
