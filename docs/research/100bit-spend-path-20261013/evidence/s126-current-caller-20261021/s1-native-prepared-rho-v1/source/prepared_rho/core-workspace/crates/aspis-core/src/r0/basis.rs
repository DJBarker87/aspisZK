//! SPEC §3: Chebyshev-product natural basis and coefficient conversions.

use super::{CodeField, Error};
use crate::field::M31;
use alloc::vec::Vec;

/// SPEC §3: evaluate D_b, with D_0=X, D_(b+1)=2 D_b²−1.
pub fn doubled_factor<E: CodeField>(b: usize, x: E) -> E {
    let mut d = x;
    for _ in 0..b {
        d = double(d);
    }
    d
}

pub(crate) fn double<E: CodeField>(x: E) -> E {
    let square = x.mul(x);
    square.add(square).sub(E::ONE)
}

/// SPEC §3: evaluate N_j=∏_{b in bits(j)} D_b (including N_0=1).
pub fn natural<E: CodeField>(mut j: usize, x: E) -> E {
    let mut factor = x;
    let mut out = E::ONE;
    while j != 0 {
        if j & 1 != 0 {
            out = out.mul(factor);
        }
        j >>= 1;
        if j != 0 {
            factor = double(factor);
        }
    }
    out
}

pub(crate) fn values<E: CodeField, const N: usize>(x: E) -> [E; N] {
    let mut out = [E::ONE; N];
    let mut width = 1;
    let mut factor = x;
    while width < N {
        for j in 0..width.min(N - width) {
            out[width + j] = out[j].mul(factor);
        }
        width *= 2;
        factor = double(factor);
    }
    out
}

/// The only two conversion sizes in SPEC §3.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BasisSize {
    Initial,
    Final,
}

impl BasisSize {
    pub const fn len(self) -> usize {
        match self {
            Self::Initial => 512,
            Self::Final => 256,
        }
    }
    pub const fn is_empty(self) -> bool {
        false
    }
}

/// SPEC §3: M_n[d,j]=[X^d]N_j and M_n⁻¹, in row-major order.
///
/// Entries lie in F; application embeds them into any CodeField. Generation
/// uses D's polynomial recurrence, then triangular back-substitution. No
/// elimination in E or huge stack-resident matrix is needed. Retain/reuse this
/// object across chord operations (M_512 and its inverse take 2 MiB total).
pub struct NaturalBasis {
    size: BasisSize,
    matrix: Vec<M31>,
    inverse: Vec<M31>,
}

fn zero_vec(len: usize) -> Result<Vec<M31>, Error> {
    let mut result = Vec::new();
    result
        .try_reserve_exact(len)
        .map_err(|_| Error::Allocation)?;
    result.resize(len, M31::ZERO);
    Ok(result)
}

impl NaturalBasis {
    /// SPEC §3: generate M_512/M_256 and their inverses from the recurrence.
    pub fn new(size: BasisSize) -> Result<Self, Error> {
        let n = size.len();
        let mut matrix = zero_vec(n * n)?;
        let mut inverse = zero_vec(n * n)?;
        let mut d = zero_vec(n)?;
        let mut next = zero_vec(n)?;
        matrix[0] = M31::ONE;
        d[1] = M31::ONE;
        let mut width = 1;
        while width < n {
            // N_(width+j)=D_log2(width)*N_j, for j<width.
            for j in 0..width {
                for k in 0..=width {
                    if d[k] == M31::ZERO {
                        continue;
                    }
                    for t in 0..=j {
                        let old = matrix[t * n + j];
                        if old != M31::ZERO {
                            let index = (k + t) * n + width + j;
                            matrix[index] = matrix[index].add(d[k].mul(old));
                        }
                    }
                }
            }
            width *= 2;
            if width < n {
                next.fill(M31::ZERO);
                for k in 0..=width / 2 {
                    if d[k] == M31::ZERO {
                        continue;
                    }
                    for t in 0..=width / 2 {
                        next[k + t] = next[k + t].add(d[k].mul(d[t]).double());
                    }
                }
                next[0] = next[0].sub(M31::ONE);
                core::mem::swap(&mut d, &mut next);
            }
        }
        for j in 0..n {
            let diagonal =
                <M31 as CodeField>::try_inv(matrix[j * n + j]).ok_or(Error::ZeroDenominator)?;
            inverse[j * n + j] = diagonal;
            for i in (0..j).rev() {
                let mut sum = M31::ZERO;
                for k in i + 1..=j {
                    let a = matrix[i * n + k];
                    let b = inverse[k * n + j];
                    if a != M31::ZERO && b != M31::ZERO {
                        sum = sum.add(a.mul(b));
                    }
                }
                // Previously computed diagonal inverse of row i.
                inverse[i * n + j] = sum.neg().mul(inverse[i * n + i]);
            }
        }
        Ok(Self {
            size,
            matrix,
            inverse,
        })
    }

    pub const fn size(&self) -> BasisSize {
        self.size
    }
    pub fn matrix(&self) -> &[M31] {
        &self.matrix
    }
    pub fn inverse_matrix(&self) -> &[M31] {
        &self.inverse
    }

    /// SPEC §3: M * natural coefficients; both slices must have size n.
    pub fn natural_to_monomial<E: CodeField>(
        &self,
        input: &[E],
        output: &mut [E],
    ) -> Result<(), Error> {
        self.apply(&self.matrix, false, input, output)
    }
    /// SPEC §3: M⁻¹ * monomial coefficients; both slices must have size n.
    pub fn monomial_to_natural<E: CodeField>(
        &self,
        input: &[E],
        output: &mut [E],
    ) -> Result<(), Error> {
        self.apply(&self.inverse, false, input, output)
    }
    pub(crate) fn transpose<E: CodeField>(
        &self,
        inverse: bool,
        input: &[E],
        output: &mut [E],
    ) -> Result<(), Error> {
        self.apply(
            if inverse { &self.inverse } else { &self.matrix },
            true,
            input,
            output,
        )
    }
    fn apply<E: CodeField>(
        &self,
        matrix: &[M31],
        transpose: bool,
        input: &[E],
        output: &mut [E],
    ) -> Result<(), Error> {
        let n = self.size.len();
        if input.len() != n || output.len() != n {
            return Err(Error::WrongLength);
        }
        output.fill(E::ZERO);
        for row in 0..n {
            for col in row..n {
                let scalar = matrix[row * n + col];
                if scalar == M31::ZERO {
                    continue;
                }
                let (dst, src) = if transpose { (col, row) } else { (row, col) };
                output[dst] = output[dst].add(E::from_m31(scalar).mul(input[src]));
            }
        }
        Ok(())
    }
}
