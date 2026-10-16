//! SPEC §5: exact secant normalization, interpolation, and the chord map.

use super::{
    basis::{BasisSize, NaturalBasis},
    domain::{self, InitialIndex, Point},
    CodeField, Error, Message,
};

pub fn secant_a<E: CodeField>(z0: Point<E>, z1: Point<E>) -> E {
    z0.x.mul(z1.y).sub(z1.x.mul(z0.y))
}
pub fn secant_b<E: CodeField>(z0: Point<E>, z1: Point<E>) -> E {
    z0.y.sub(z1.y)
}
pub fn secant_c<E: CodeField>(z0: Point<E>, z1: Point<E>) -> E {
    z1.x.sub(z0.x)
}

/// SPEC §5: (a,b,c) in the cited normalization, with no rescaling.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Secant<E> {
    pub a: E,
    pub b: E,
    pub c: E,
}
impl<E: CodeField> Secant<E> {
    /// Algebraic formula only: no point policy is silently imposed. The
    /// no-domain-zero theorem requires distinct non-F-rational circle points.
    pub fn from_points(z0: Point<E>, z1: Point<E>) -> Self {
        Self {
            a: secant_a(z0, z1),
            b: secant_b(z0, z1),
            c: secant_c(z0, z1),
        }
    }
    pub fn eval(self, point: Point<E>) -> E {
        self.a.add(self.b.mul(point.x)).add(self.c.mul(point.y))
    }
    /// SPEC §5: L(z0,z1)[i]=a+b*X_i+c*Y_i.
    pub fn line_word(self, i: InitialIndex) -> E {
        self.eval(domain::stored_point(i))
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Axis {
    X,
    Y,
}
impl Axis {
    pub fn coordinate<E: Copy>(self, z: Point<E>) -> E {
        match self {
            Self::X => z.x,
            Self::Y => z.y,
        }
    }
}
/// SPEC §5: prefer x when x1!=x0, otherwise y (including coincident inputs).
pub fn axis<E: CodeField>(z0: Point<E>, z1: Point<E>) -> Axis {
    if z1.x != z0.x {
        Axis::X
    } else {
        Axis::Y
    }
}
pub fn delta<E: CodeField>(z0: Point<E>, z1: Point<E>) -> E {
    let axis = axis(z0, z1);
    axis.coordinate(z1).sub(axis.coordinate(z0))
}

/// Monomial pair p0[0]+p0[1]*X, p1. SPEC §5 interpolationPair.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct InterpolationPair<E> {
    pub p0: [E; 2],
    pub p1: E,
}
pub fn interpolation_pair<E: CodeField>(
    z0: Point<E>,
    z1: Point<E>,
    y: [E; 2],
) -> Result<InterpolationPair<E>, Error> {
    let slope = y[1]
        .sub(y[0])
        .mul(delta(z0, z1).try_inv().ok_or(Error::ZeroDenominator)?);
    Ok(match axis(z0, z1) {
        Axis::X => InterpolationPair {
            p0: [y[0].sub(slope.mul(z0.x)), slope],
            p1: E::ZERO,
        },
        Axis::Y => InterpolationPair {
            p0: [y[0].sub(slope.mul(z0.y)), E::ZERO],
            p1: slope,
        },
    })
}
/// SPEC §5: the 1024 natural coefficients of liftLinear(interpolationPair).
pub fn interpolant<E: CodeField>(
    z0: Point<E>,
    z1: Point<E>,
    y: [E; 2],
) -> Result<Message<E>, Error> {
    let pair = interpolation_pair(z0, z1, y)?;
    let mut result = [E::ZERO; 1024];
    result[0] = pair.p0[0];
    result[1] = pair.p1;
    result[2] = pair.p0[1];
    Ok(result)
}

fn check_basis(basis: &NaturalBasis) -> Result<(), Error> {
    if basis.size() == BasisSize::Initial {
        Ok(())
    } else {
        Err(Error::WrongLength)
    }
}
fn halves<E: CodeField>(q: &Message<E>) -> ([E; 512], [E; 512]) {
    (
        core::array::from_fn(|j| q[2 * j]),
        core::array::from_fn(|j| q[2 * j + 1]),
    )
}
fn interleave<E: CodeField>(a: [E; 512], b: [E; 512]) -> Message<E> {
    core::array::from_fn(|j| if j % 2 == 0 { a[j / 2] } else { b[j / 2] })
}
/// SPEC §§3,5: monomial coefficient arrays for p0_q and p1_q.
pub fn polynomial_pair<E: CodeField>(
    basis: &NaturalBasis,
    q: &Message<E>,
) -> Result<([E; 512], [E; 512]), Error> {
    check_basis(basis)?;
    let (a, b) = halves(q);
    let (mut p, mut r) = ([E::ZERO; 512], [E::ZERO; 512]);
    basis.natural_to_monomial(&a, &mut p)?;
    basis.natural_to_monomial(&b, &mut r)?;
    Ok((p, r))
}
/// SPEC §5: monomial truncation to 0..511, M_512⁻¹, then interleave.
/// Slices are increasing-degree monomial coefficients, with zero extension
/// for short polynomials. Coefficients above degree 511 are discarded.
pub fn lift_linear<E: CodeField>(
    basis: &NaturalBasis,
    p: &[E],
    r: &[E],
) -> Result<Message<E>, Error> {
    check_basis(basis)?;
    let p = core::array::from_fn::<_, 512, _>(|j| p.get(j).copied().unwrap_or(E::ZERO));
    let r = core::array::from_fn::<_, 512, _>(|j| r.get(j).copied().unwrap_or(E::ZERO));
    let (mut a, mut b) = ([E::ZERO; 512], [E::ZERO; 512]);
    basis.monomial_to_natural(&p, &mut a)?;
    basis.monomial_to_natural(&r, &mut b)?;
    Ok(interleave(a, b))
}
/// SPEC §5: chordMessage/chordLinear, including monomial truncation off-image.
pub fn chord_message<E: CodeField>(
    basis: &NaturalBasis,
    line: Secant<E>,
    q: &Message<E>,
) -> Result<Message<E>, Error> {
    let (p, r) = polynomial_pair(basis, q)?;
    let (mut h0, mut h1) = ([E::ZERO; 512], [E::ZERO; 512]);
    for d in 0..512 {
        h0[d] = line.a.mul(p[d]).add(line.c.mul(r[d]));
        h1[d] = line.c.mul(p[d]).add(line.a.mul(r[d]));
        if d > 0 {
            h0[d] = h0[d].add(line.b.mul(p[d - 1]));
            h1[d] = h1[d].add(line.b.mul(r[d - 1]));
        }
        if d > 1 {
            h0[d] = h0[d].sub(line.c.mul(r[d - 2]));
        }
    }
    lift_linear(basis, &h0, &h1)
}
/// SPEC §5: C[a,b,c]^T*w, the transpose of multiplication followed by lift.
/// Evaluates the transposed factors M^T A^T M^(-T) in O(512²), retaining
/// precisely the same top-entry truncation as chord_message, for every q.
pub fn quotient_weights<E: CodeField>(
    basis: &NaturalBasis,
    line: Secant<E>,
    w: &Message<E>,
) -> Result<Message<E>, Error> {
    check_basis(basis)?;
    let (we, wo) = halves(w);
    let (mut u, mut v) = ([E::ZERO; 512], [E::ZERO; 512]);
    basis.transpose(true, &we, &mut u)?;
    basis.transpose(true, &wo, &mut v)?;
    let (mut h0, mut h1) = ([E::ZERO; 512], [E::ZERO; 512]);
    for d in 0..512 {
        h0[d] = line.a.mul(u[d]).add(line.c.mul(v[d]));
        h1[d] = line.c.mul(u[d]).add(line.a.mul(v[d]));
        if d + 1 < 512 {
            h0[d] = h0[d].add(line.b.mul(u[d + 1]));
            h1[d] = h1[d].add(line.b.mul(v[d + 1]));
        }
        if d + 2 < 512 {
            h1[d] = h1[d].sub(line.c.mul(u[d + 2]));
        }
    }
    let (mut a, mut b) = ([E::ZERO; 512], [E::ZERO; 512]);
    basis.transpose(false, &h0, &mut a)?;
    basis.transpose(false, &h1, &mut b)?;
    Ok(interleave(a, b))
}

/// SPEC §5: FunctionalWeights.row(f)[j]=f(epsilon_j).
/// The caller supplies a linear functional; linearity is a mathematical
/// precondition, not something this finite row constructor attempts to infer.
pub struct FunctionalWeights;
impl FunctionalWeights {
    pub fn row<E: CodeField>(mut f: impl FnMut(&Message<E>) -> E) -> Message<E> {
        let mut unit = [E::ZERO; 1024];
        let mut row = [E::ZERO; 1024];
        for j in 0..1024 {
            unit[j] = E::ONE;
            row[j] = f(&unit);
            unit[j] = E::ZERO;
        }
        row
    }
    /// SPEC §5: row(e1)[2k+1]=M[511,k], even entries zero.
    pub fn e1<E: CodeField>(basis: &NaturalBasis) -> Result<Message<E>, Error> {
        check_basis(basis)?;
        Ok(core::array::from_fn(|j| {
            if j % 2 == 0 {
                E::ZERO
            } else {
                E::from_m31(basis.matrix()[511 * 512 + j / 2])
            }
        }))
    }
    /// SPEC §5: row(e2)[2k]=b*M[511,k], row(e2)[2k+1]=-c*M[510,k].
    pub fn e2<E: CodeField>(basis: &NaturalBasis, b: E, c: E) -> Result<Message<E>, Error> {
        check_basis(basis)?;
        Ok(core::array::from_fn(|j| {
            if j % 2 == 0 {
                b.mul(E::from_m31(basis.matrix()[511 * 512 + j / 2]))
            } else {
                c.neg().mul(E::from_m31(basis.matrix()[510 * 512 + j / 2]))
            }
        }))
    }
}
fn coefficient<E: CodeField>(
    basis: &NaturalBasis,
    q: &Message<E>,
    degree: usize,
    parity: usize,
) -> E {
    (degree..512).fold(E::ZERO, |sum, j| {
        sum.add(E::from_m31(basis.matrix()[degree * 512 + j]).mul(q[2 * j + parity]))
    })
}
/// SPEC §5: [X^511]p1_q.
pub fn e1<E: CodeField>(basis: &NaturalBasis, q: &Message<E>) -> Result<E, Error> {
    check_basis(basis)?;
    Ok(coefficient(basis, q, 511, 1))
}
/// SPEC §5: b*[X^511]p0_q−c*[X^510]p1_q.
pub fn e2<E: CodeField>(basis: &NaturalBasis, b: E, c: E, q: &Message<E>) -> Result<E, Error> {
    check_basis(basis)?;
    Ok(b.mul(coefficient(basis, q, 511, 0))
        .sub(c.mul(coefficient(basis, q, 510, 1))))
}
