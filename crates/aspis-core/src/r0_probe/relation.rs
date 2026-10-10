//! P1 C2 cost experiment: three degree-six rounds and a four-term terminal.
//! The round loop follows main's v6_onefold_prover V7Compact tail structure.
use super::{
    fold, heap, onchain,
    opening::{powers, OpeningData},
    structured, structured_k,
    wire::{OpeningProof, OpeningView},
    Error,
};
use crate::{
    field::{WideExact as E, QM31},
    r0_transcript, HashFn,
};
use alloc::vec::Vec;
pub const BYTES: usize = 3 * 7 * 32;
pub struct Proof {
    pub opening: OpeningProof,
    pub rounds: Vec<[E; 7]>,
}
impl Proof {
    pub fn encode(&self) -> Result<Vec<u8>, Error> {
        if self.rounds.len() != 3 {
            return Err(Error::WrongLength);
        }
        let mut out = self.opening.encode()?;
        out.try_reserve_exact(BYTES)
            .map_err(|_| Error::Allocation)?;
        for c in &self.rounds {
            for x in c {
                out.extend_from_slice(&x.to_le_bytes());
            }
        }
        Ok(out)
    }
}
fn eval(c: &[E; 7], a: E) -> E {
    c.iter().rev().fold(E::ZERO, |v, &x| v.mul(a).add(x))
}
fn challenge(hash: HashFn, state: &mut [u8; 32], round: usize, c: &[E; 7]) -> E {
    let mut bytes = [0u8; 224];
    for (dst, x) in bytes.chunks_exact_mut(32).zip(c) {
        dst.copy_from_slice(&x.to_le_bytes());
    }
    let absorbed = hash(&[
        state,
        &[0, 0xc1 + round as u8],
        &[0x21 + round as u8],
        &224u32.to_le_bytes(),
        &bytes,
    ]);
    let block = hash(&[&absorbed, &[1]]);
    *state = hash(&[&absorbed, &[2]]);
    r0_transcript::ordinary_sample(&block)
}
fn fold_values(v: &mut Vec<E>, a: E, dual: bool) {
    let n = v.len() / 4;
    for j in 0..n {
        let h = [v[4 * j], v[4 * j + 1], v[4 * j + 2], v[4 * j + 3]];
        let h = if dual { [h[0], h[3], h[2], h[1]] } else { h };
        v[j] = h[0].add(a.mul(h[1].add(a.mul(h[2].add(a.mul(h[3]))))));
    }
    v.truncate(n);
}
fn dot(q: &[E], w: &[E]) -> E {
    q.iter().zip(w).fold(E::ZERO, |s, (&q, &w)| s.add(q.mul(w)))
}
fn polynomial(q: &[E], w: &[E]) -> [E; 7] {
    let mut c = [E::ZERO; 7];
    let rho = [0, 3, 2, 1];
    for d in 0..q.len() / 4 {
        for s in 0..4 {
            for t in 0..4 {
                c[s + rho[t]] = c[s + rho[t]].add(q[4 * d + s].mul(w[4 * d + t]));
            }
        }
    }
    c
}
pub fn prove(
    hash: HashFn,
    mut state: [u8; 32],
    alpha0: E,
    w: &[E; 1024],
    f: &[E; 256],
    incoming: E,
) -> Result<Vec<[E; 7]>, Error> {
    let mut q = f.to_vec();
    let mut w = w.to_vec();
    fold_values(&mut w, alpha0, true);
    for x in &mut w {
        *x = x.mul(fold::quarter());
    }
    if dot(&q, &w) != incoming {
        return Err(Error::V2);
    }
    let mut claim = incoming;
    let mut rounds = Vec::with_capacity(3);
    for round in 0..3 {
        let c = polynomial(&q, &w);
        if c[0].add(c[4]) != claim {
            return Err(Error::V2);
        }
        let a = challenge(hash, &mut state, round, &c);
        claim = eval(&c, a);
        fold_values(&mut q, a, false);
        fold_values(&mut w, a, true);
        if dot(&q, &w) != claim {
            return Err(Error::V2);
        }
        rounds.push(c);
    }
    if q.len() != 4 || w.len() != 4 {
        return Err(Error::WrongLength);
    }
    Ok(rounds)
}
#[inline(never)]
fn initial_weights(data: &OpeningData, kappa: E, tau: E, alpha: E) -> Result<Vec<E>, Error> {
    if kappa.c1() != QM31::ZERO || tau.c1() != QM31::ZERO {
        return Err(Error::WrongField);
    }
    let mut w = onchain::weights_k(data, kappa.c0())?;
    let mut even = heap::filled(512, QM31::ZERO)?;
    let mut odd = heap::filled(512, QM31::ZERO)?;
    let mut twice = heap::filled(512, QM31::ZERO)?;
    let line = onchain::subfield_line(data)?;
    structured_k::quotient_weights(line, &mut w, &mut even, &mut odd, &mut twice)?;
    let tau = tau.c0();
    let tau2 = tau.mul(tau);
    let top = structured::top_rows(511)[1];
    w[1023] = w[1023].add(tau.mul_m31(top));
    w[1022] = w[1022].add(tau2.mul(line.b.mul_m31(top)));
    w[1021] = w[1021].add(tau2.mul(line.c.neg().mul_m31(structured::top_rows(510)[0])));
    let a = powers::<4>(alpha);
    let mut out = heap::filled(256, E::ZERO)?;
    for j in 0..256 {
        let h = &w[4 * j..4 * j + 4];
        out[j] = E::from_qm31(h[0])
            .add(a[1].mul_qm31(h[3]))
            .add(a[2].mul_qm31(h[2]))
            .add(a[3].mul_qm31(h[1]))
            .mul_m31(crate::field::M31_QUARTER);
    }
    Ok(out)
}
#[inline(never)]
pub fn verify(
    hash: HashFn,
    mut state: [u8; 32],
    data: &OpeningData,
    kappa: E,
    tau: E,
    alpha0: E,
    p0: &[E; 7],
    proof: &OpeningView<'_>,
    bytes: &[u8],
) -> Result<(), Error> {
    if bytes.len() != BYTES {
        return Err(Error::Parse);
    }
    let mut claim = eval(p0, alpha0);
    let mut w = initial_weights(data, kappa, tau, alpha0)?;
    let mut q = heap::filled(256, E::ZERO)?;
    for j in 0..256 {
        q[j] = proof.final_coefficient(j);
    }
    for round in 0..3 {
        let mut c = [E::ZERO; 7];
        for j in 0..7 {
            let start = (7 * round + j) * 32;
            c[j] = E::from_le_bytes(&bytes[start..start + 32]).ok_or(Error::NonCanonical)?;
        }
        if c[0].add(c[4]) != claim {
            return Err(Error::V2);
        }
        let a = challenge(hash, &mut state, round, &c);
        claim = eval(&c, a);
        fold_values(&mut q, a, false);
        fold_values(&mut w, a, true);
    }
    if q.len() != 4 || w.len() != 4 || dot(&q, &w) != claim {
        return Err(Error::V2);
    }
    Ok(())
}
