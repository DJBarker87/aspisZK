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
    queries: &[u32; 22],
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
    #[cfg(feature = "r0-probe-c3")]
    {
        let mut batch = QueryBatch::new(hash, state);
        for &u in queries {
            batch.add(final_at(f, u)?);
        }
        add_dense_queries(&mut w, queries, batch.rho)?;
        claim = claim.add(batch.claim);
        state = batch.bind_claim(hash);
    }

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
    queries: &[u32; 22],
    query: Option<&QueryBatch>,
) -> Result<(), Error> {
    if bytes.len() != BYTES {
        return Err(Error::Parse);
    }
    let mut claim = eval(p0, alpha0);
    let mut w = initial_weights(data, kappa, tau, alpha0)?;
    #[cfg(feature = "r0-probe-c3")]
    {
        let batch = query.ok_or(Error::Schedule)?;
        claim = claim.add(batch.claim);
        state = batch.bind_claim(hash);
    }
    #[cfg(feature = "r0-probe-c3")]
    let mut alphas = [E::ZERO; 3];
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
        #[cfg(feature = "r0-probe-c3")]
        {
            alphas[round] = a;
        }
        fold_values(&mut q, a, false);
        fold_values(&mut w, a, true);
    }
    #[cfg(feature = "r0-probe-c3")]
    {
        let batch = query.ok_or(Error::Schedule)?;
        let extra = folded_queries(queries, batch.rho, &alphas)?;
        #[cfg(all(feature = "r0-probe-reference", not(target_os = "solana")))]
        {
            let mut dense = heap::filled(256, E::ZERO)?;
            add_dense_queries(&mut dense, queries, batch.rho)?;
            for &a in &alphas {
                fold_values(&mut dense, a, true);
            }
            assert_eq!(
                extra.as_slice(),
                dense.as_slice(),
                "query tensor differs from dense predecessor coefficients"
            );
        }
        for j in 0..4 {
            w[j] = w[j].add(extra[j]);
        }
    }
    if q.len() != 4 || w.len() != 4 || dot(&q, &w) != claim {
        return Err(Error::V2);
    }
    Ok(())
}

/// P1 C3 batch state, sampled after F and the query set.
pub struct QueryBatch {
    state: [u8; 32],
    pub rho: E,
    pub claim: E,
    next: E,
}
impl QueryBatch {
    pub fn new(hash: HashFn, state: [u8; 32]) -> Self {
        let absorbed = hash(&[&state, &[0, 0xb0], &[0x30], &0u32.to_le_bytes()]);
        let block = hash(&[&absorbed, &[1]]);
        let state = hash(&[&absorbed, &[2]]);
        let rho = r0_transcript::ordinary_sample(&block);
        Self {
            state,
            rho,
            claim: E::ZERO,
            next: rho,
        }
    }
    pub fn add(&mut self, value: E) {
        self.claim = self.claim.add(self.next.mul(value));
        self.next = self.next.mul(self.rho);
    }
    fn bind_claim(&self, hash: HashFn) -> [u8; 32] {
        hash(&[
            &self.state,
            &[0, 0xb1],
            &[0x31],
            &32u32.to_le_bytes(),
            &self.claim.to_le_bytes(),
        ])
    }
}
fn final_at(f: &[E; 256], u: u32) -> Result<E, Error> {
    let u = super::domain::FibreIndex::new(u as usize)?;
    let b = super::basis::values::<crate::field::M31, 256>(super::domain::line_node(u));
    Ok(f.iter()
        .zip(b)
        .fold(E::ZERO, |s, (&f, b)| s.add(f.mul_m31(b))))
}
fn add_dense_queries(w: &mut [E], queries: &[u32; 22], rho: E) -> Result<(), Error> {
    let mut scale = rho;
    for &u in queries {
        let u = super::domain::FibreIndex::new(u as usize)?;
        let b = super::basis::values::<crate::field::M31, 256>(super::domain::line_node(u));
        for j in 0..256 {
            w[j] = w[j].add(scale.mul_m31(b[j]));
        }
        scale = scale.mul(rho);
    }
    Ok(())
}
#[inline(never)]
fn folded_queries(queries: &[u32; 22], rho: E, alphas: &[E; 3]) -> Result<[E; 4], Error> {
    use crate::field::M31;
    let powers = alphas.map(powers::<4>);
    let mut out = [E::ZERO; 4];
    let mut scale = rho;
    for &u in queries {
        let mut x = super::domain::line_node::<M31>(super::domain::FibreIndex::new(u as usize)?);
        let mut s = scale;
        for a in &powers {
            let y = super::basis::double(x);
            let factor = E::ONE
                .add(a[3].mul_m31(x))
                .add(a[2].mul_m31(y))
                .add(a[1].mul_m31(x.mul(y)));
            s = s.mul(factor);
            x = super::basis::double(y);
        }
        let y = super::basis::double(x);
        for (j, b) in [M31::ONE, x, y, x.mul(y)].into_iter().enumerate() {
            out[j] = out[j].add(s.mul_m31(b));
        }
        scale = scale.mul(rho);
    }
    Ok(out)
}
#[cfg(all(feature = "r0-probe-reference", not(target_os = "solana")))]
pub fn reference_query_batch(
    hash: HashFn,
    state: [u8; 32],
    proof: &OpeningView<'_>,
    queries: &[u32; 22],
) -> Result<QueryBatch, Error> {
    let mut batch = QueryBatch::new(hash, state);
    for &u in queries {
        let u = super::domain::FibreIndex::new(u as usize)?;
        let b = super::basis::values::<crate::field::M31, 256>(super::domain::line_node(u));
        let value = (0..256).fold(E::ZERO, |s, j| {
            s.add(proof.final_coefficient(j).mul_m31(b[j]))
        });
        batch.add(value);
    }
    Ok(batch)
}
