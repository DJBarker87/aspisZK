//! SPEC §§6–9: full-size commitments and the honest opening prover.
use super::{
    basis::{self, NaturalBasis},
    chord,
    domain::{self, FibreIndex, Point},
    encoder, fold,
    merkle::{self, filled, Tree},
    opening::{self, Claims, Endpoints, LANES},
    transcript::{OpeningTranscript, SemanticBoundary},
    transport,
    wire::{FibreOpening, OpeningProof},
    CodeField, Error, Message, FIBRE_COUNT, WORD_LEN,
};
use crate::{
    field::{WideExact as E, M31, QM31},
    HashFn,
};
use alloc::vec::Vec;

/// Natural-product evaluation tree. Coordinates are always in F.
pub struct EncodingDomain {
    xy: Vec<Point<M31>>,
    levels: Vec<Vec<M31>>,
}
impl EncodingDomain {
    pub fn new() -> Result<Self, Error> {
        let mut xy = filled(
            FIBRE_COUNT,
            Point {
                x: M31::ZERO,
                y: M31::ZERO,
            },
        )?;
        for (u, z) in xy.iter_mut().enumerate() {
            *z = domain::fibre_point(FibreIndex::new(u)?);
        }
        let mut levels = Vec::new();
        levels.try_reserve_exact(9).map_err(|_| Error::Allocation)?;
        let mut first = filled(FIBRE_COUNT, M31::ZERO)?;
        for (n, z) in first.iter_mut().zip(&xy) {
            *n = basis::double(z.x);
        }
        levels.push(first);
        for depth in 0..8 {
            let mut next = filled(levels[depth].len() / 2, M31::ZERO)?;
            for (j, n) in next.iter_mut().enumerate() {
                *n = basis::double(levels[depth][2 * j]);
            }
            levels.push(next);
        }
        Ok(Self { xy, levels })
    }
    fn evaluate<T: CodeField>(&self, coefficients: &[T], depth: usize) -> Result<Vec<T>, Error> {
        let nodes = &self.levels[depth];
        if coefficients.len() == 1 {
            return filled(nodes.len(), coefficients[0]);
        }
        let mut even = filled(coefficients.len() / 2, T::ZERO)?;
        let mut odd = filled(even.len(), T::ZERO)?;
        for j in 0..even.len() {
            even[j] = coefficients[2 * j];
            odd[j] = coefficients[2 * j + 1];
        }
        let a = self.evaluate(&even, depth + 1)?;
        let b = self.evaluate(&odd, depth + 1)?;
        let mut out = filled(nodes.len(), T::ZERO)?;
        for j in 0..nodes.len() {
            out[j] = a[j / 2].add(T::from_m31(nodes[j]).mul(b[j / 2]));
        }
        Ok(out)
    }
    /// Exact §3 encoder at every stored index, O(N log 1024), using
    /// N_(2j)(x)=N_j(2x²−1), N_(2j+1)(x)=x*N_j(2x²−1).
    pub fn encode<T: CodeField>(&self, message: &Message<T>) -> Result<Vec<T>, Error> {
        let mut channels = Vec::new();
        channels
            .try_reserve_exact(4)
            .map_err(|_| Error::Allocation)?;
        for s in 0..4 {
            let coeff = core::array::from_fn::<_, 256, _>(|d| message[4 * d + s]);
            channels.push(self.evaluate(&coeff, 0)?);
        }
        let mut word = filled(WORD_LEN, T::ZERO)?;
        for (u, z) in self.xy.iter().enumerate() {
            let values = fold::phi_inverse(
                T::from_m31(z.x),
                T::from_m31(z.y),
                core::array::from_fn(|s| channels[s][u]),
            );
            word[4 * u..4 * u + 4].copy_from_slice(&values);
        }
        Ok(word)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CommitmentTime {
    C1,
    C2,
}
enum Word {
    Base(Vec<M31>),
    Secure(Vec<QM31>),
}
impl Word {
    fn value(&self, i: usize) -> E {
        match self {
            Self::Base(w) => E::from_m31(w[i]),
            Self::Secure(w) => E::from_qm31(w[i]),
        }
    }
}
/// C1 can be constructed before λ/χ; C2 separately after them. The 29-entry
/// input permits virtual lanes but only this time's lanes are committed.
pub struct Commitment {
    time: CommitmentTime,
    lanes: Vec<usize>,
    messages: Vec<Message<E>>,
    words: Vec<Word>,
    tree: Tree,
}
impl Commitment {
    pub fn new(
        hash: HashFn,
        domain: &EncodingDomain,
        time: CommitmentTime,
        messages: &[Message<E>],
    ) -> Result<Self, Error> {
        if messages.len() != LANES {
            return Err(Error::WrongLength);
        }
        let indices: &[usize] = match time {
            CommitmentTime::C1 => &[
                0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22,
                23, 24, 25, 28,
            ],
            CommitmentTime::C2 => &[26, 27],
        };
        let mut lanes = filled(indices.len(), 0)?;
        lanes.copy_from_slice(indices);
        let mut words = Vec::new();
        words
            .try_reserve_exact(lanes.len())
            .map_err(|_| Error::Allocation)?;
        let mut saved = Vec::new();
        saved
            .try_reserve_exact(lanes.len())
            .map_err(|_| Error::Allocation)?;
        for &l in &lanes {
            if messages[l].iter().any(|x| {
                x.to_limbs()[if l < 26 { 1 } else { 4 }..]
                    .iter()
                    .any(|&d| d != 0)
            }) {
                return Err(Error::WrongField);
            }
            // API inputs and retained matching data are semantic rows; only
            // Enc consumes coefficients. W_l = Enc(t_l ∘ π⁻¹), D13.
            let coefficients = transport::to_coefficients(&messages[l]);
            words.push(if l < 26 {
                Word::Base(domain.encode(&coefficients.map(|x| M31(x.to_limbs()[0])))?)
            } else {
                Word::Secure(domain.encode(&coefficients.map(|x| x.c0()))?)
            });
            saved.push(messages[l]);
        }
        let mut leaves = filled(FIBRE_COUNT, [0; 32])?;
        for (u, digest) in leaves.iter_mut().enumerate() {
            let mut bytes = [0u8; 480];
            let mut at = 0;
            for s in 0..4 {
                for (j, &l) in lanes.iter().enumerate() {
                    let b = words[j].value(4 * u + s).to_le_bytes();
                    let width = if l < 26 { 4 } else { 16 };
                    bytes[at..at + width].copy_from_slice(&b[..width]);
                    at += width;
                }
            }
            *digest = merkle::leaf(
                hash,
                if time == CommitmentTime::C1 {
                    merkle::C1_TAG
                } else {
                    merkle::C2_TAG
                },
                &bytes[..at],
            );
        }
        Ok(Self {
            time,
            lanes,
            messages: saved,
            words,
            tree: Tree::new(hash, leaves)?,
        })
    }
    pub fn root(&self) -> [u8; 32] {
        self.tree.root()
    }
    fn matches(&self, messages: &[Message<E>]) -> bool {
        self.lanes
            .iter()
            .enumerate()
            .all(|(j, &l)| self.messages[j] == messages[l])
    }
    pub(crate) fn fill_opening(&self, u: FibreIndex, out: &mut FibreOpening) {
        for (j, &l) in self.lanes.iter().enumerate() {
            for s in 0..4 {
                out.values[s][l] = self.words[j].value(4 * u.get() + s);
            }
        }
        out.paths[if self.time == CommitmentTime::C1 {
            0
        } else {
            1
        }] = self.tree.path(u);
    }
}

// Sparse Gaussian elimination of the §5 matrix AFTER the invertible
// M_512 change of coordinates. Highest-column pivots keep the convolution
// equations banded; no dense 1024^3 elimination, division decoder, or FFT
// assumption is used. e1/e2 are literal extra rows, not postulated premises.
struct Row {
    terms: Vec<(usize, E)>,
    rhs: E,
}
impl Row {
    fn new(rhs: E) -> Result<Self, Error> {
        let mut terms = Vec::new();
        terms.try_reserve_exact(8).map_err(|_| Error::Allocation)?;
        Ok(Self { terms, rhs })
    }
    fn add(&mut self, col: usize, value: E) -> Result<(), Error> {
        if value == E::ZERO {
            return Ok(());
        }
        if let Some(i) = self.terms.iter().position(|&(c, _)| c == col) {
            self.terms[i].1 = self.terms[i].1.add(value);
            if self.terms[i].1 == E::ZERO {
                self.terms.swap_remove(i);
            }
        } else {
            self.terms.try_reserve(1).map_err(|_| Error::Allocation)?;
            self.terms.push((col, value));
        }
        Ok(())
    }
}
fn insert(mut row: Row, pivots: &mut [Option<Row>]) -> Result<(), Error> {
    while let Some(&(col, value)) = row.terms.iter().max_by_key(|&&(c, _)| c) {
        if let Some(pivot) = &pivots[col] {
            for &(j, c) in &pivot.terms {
                row.add(j, value.mul(c).neg())?;
            }
            row.rhs = row.rhs.sub(value.mul(pivot.rhs));
        } else {
            let inverse = value.try_inv().ok_or(Error::ZeroDenominator)?;
            for (_, v) in &mut row.terms {
                *v = v.mul(inverse);
            }
            row.rhs = row.rhs.mul(inverse);
            pivots[col] = Some(row);
            return Ok(());
        }
    }
    if row.rhs == E::ZERO {
        Ok(())
    } else {
        Err(Error::QuotientNotInImage)
    }
}
/// Solve C*q=t−I, e1(q)=e2(q)=0 over E, with §5's M matrices.
/// Both input t and output q are natural coefficients (after D13 transport).
/// Rejects inconsistent/off-image inputs; there is no total decoder fallback.
pub fn quotient(
    basis: &NaturalBasis,
    z: [Point<E>; 2],
    t: &Message<E>,
    y: [E; 2],
) -> Result<Message<E>, Error> {
    let line = chord::Secant::from_points(z[0], z[1]);
    let interpolant = chord::interpolant(z[0], z[1], y)?;
    let rhs = core::array::from_fn(|r| t[r].sub(interpolant[r]));
    let (h0, h1) = chord::polynomial_pair(basis, &rhs)?;
    let mut pivots = Vec::new();
    pivots
        .try_reserve_exact(1024)
        .map_err(|_| Error::Allocation)?;
    pivots.resize_with(1024, || None);
    let mut e1 = Row::new(E::ZERO)?;
    e1.add(1023, E::ONE)?;
    insert(e1, &mut pivots)?;
    let mut e2 = Row::new(E::ZERO)?;
    e2.add(1022, line.b)?;
    e2.add(1021, line.c.neg())?;
    insert(e2, &mut pivots)?;
    for d in (0..512).rev() {
        let mut a = Row::new(h0[d])?;
        a.add(2 * d, line.a)?;
        a.add(2 * d + 1, line.c)?;
        if d > 0 {
            a.add(2 * (d - 1), line.b)?;
        }
        if d > 1 {
            a.add(2 * (d - 2) + 1, line.c.neg())?;
        }
        insert(a, &mut pivots)?;
        let mut b = Row::new(h1[d])?;
        b.add(2 * d, line.c)?;
        b.add(2 * d + 1, line.a)?;
        if d > 0 {
            b.add(2 * (d - 1) + 1, line.b)?;
        }
        insert(b, &mut pivots)?;
    }
    let mut solution = [E::ZERO; 1024];
    for col in 0..1024 {
        let row = pivots[col].as_ref().ok_or(Error::RankDeficient)?;
        solution[col] = row
            .terms
            .iter()
            .filter(|&&(j, _)| j != col)
            .fold(row.rhs, |v, &(j, c)| v.sub(c.mul(solution[j])));
    }
    let p = core::array::from_fn::<_, 512, _>(|d| solution[2 * d]);
    let r = core::array::from_fn::<_, 512, _>(|d| solution[2 * d + 1]);
    let q = chord::lift_linear(basis, &p, &r)?;
    if chord::chord_message(basis, line, &q)? != rhs
        || chord::e1(basis, &q)? != E::ZERO
        || chord::e2(basis, line.b, line.c, &q)? != E::ZERO
    {
        return Err(Error::QuotientNotInImage);
    }
    Ok(q)
}
/// Semantic claims over rows; D13 does not alter these claims or points.
pub fn honest_claims(messages: &[Message<E>], points: &opening::Points) -> Result<Claims, Error> {
    if messages.len() != 29 {
        return Err(Error::WrongLength);
    }
    Ok(points.map(|p| {
        let w = opening::row_eq_weight(&p);
        core::array::from_fn(|l| opening::dot(&messages[l], &w))
    }))
}
pub fn v_honest(messages: &[Message<E>], gamma: E) -> Result<E, Error> {
    if messages.len() != 29 {
        return Err(Error::WrongLength);
    }
    let g = opening::powers::<29>(gamma);
    let w = opening::indicator();
    Ok((0..29).fold(E::ZERO, |v, l| {
        v.add(g[l].mul(opening::dot(&transport::to_coefficients(&messages[l]), &w)))
    }))
}
/// SPEC §7 coefficient table, including quarter exactly once.
pub fn round_polynomial(q: &Message<E>, w: &Message<E>) -> [E; 7] {
    let mut c = [E::ZERO; 7];
    let rho = [0, 3, 2, 1];
    for d in 0..256 {
        for s in 0..4 {
            for t in 0..4 {
                c[s + rho[t]] = c[s + rho[t]].add(q[4 * d + s].mul(w[4 * d + t]));
            }
        }
    }
    c.map(|v| v.mul(fold::quarter()))
}
pub fn prove(
    hash: HashFn,
    basis: &NaturalBasis,
    boundary: &SemanticBoundary,
    messages: &[Message<E>],
    c1: &Commitment,
    c2: &Commitment,
) -> Result<OpeningProof, Error> {
    if messages.len() != 29 {
        return Err(Error::WrongLength);
    }
    if c1.time != CommitmentTime::C1
        || c2.time != CommitmentTime::C2
        || boundary.roots() != [c1.root(), c2.root()]
        || !c1.matches(messages)
        || !c2.matches(messages)
    {
        return Err(Error::Commitment);
    }
    let mut coefficients = Vec::new();
    coefficients
        .try_reserve_exact(LANES)
        .map_err(|_| Error::Allocation)?;
    coefficients.extend(messages.iter().map(transport::to_coefficients));
    let mut transcript = OpeningTranscript::new(hash, boundary);
    let z0 = transcript.z0(&boundary.claims)?;
    let y0 = core::array::from_fn(|l| encoder::eval_message(&coefficients[l], z0));
    let z1 = transcript.z1(&y0)?;
    let y: Endpoints =
        core::array::from_fn(|l| [y0[l], encoder::eval_message(&coefficients[l], z1)]);
    let data = opening::OpeningData {
        roots: boundary.roots(),
        z: [z0, z1],
        y,
        points: boundary.points(),
        claims: boundary.claims,
    };
    data.validate_points()?;
    let gamma = transcript.gamma(&y)?;
    let v = v_honest(messages, gamma)?;
    let kappa = transcript.kappa(v)?;
    let tau = transcript.tau()?;
    let mut q = [E::ZERO; 1024];
    let g = opening::powers::<29>(gamma);
    for l in 0..29 {
        let lane = quotient(basis, data.z, &coefficients[l], y[l])?;
        for r in 0..1024 {
            q[r] = q[r].add(g[l].mul(lane[r]));
        }
    }
    let w = data.total_weights(basis, kappa, tau)?;
    let c = round_polynomial(&q, &w);
    if c[0].add(c[4]) != fold::quarter::<E>().mul(data.claim_prime(gamma, v, kappa)?) {
        return Err(Error::Semantic);
    }
    let alpha = transcript.alpha(&c)?;
    let final_message = fold::fold_message(alpha, &q);
    let queries = transcript.queries(&final_message)?;
    let mut openings = Vec::new();
    openings
        .try_reserve_exact(22)
        .map_err(|_| Error::Allocation)?;
    for u in queries.sorted() {
        let mut opening = FibreOpening::empty();
        let u = FibreIndex::new(u as usize)?;
        c1.fill_opening(u, &mut opening);
        c2.fill_opening(u, &mut opening);
        openings.push(opening);
    }
    Ok(OpeningProof {
        y0,
        y,
        v,
        coefficients: [c[0], c[1], c[2], c[3], c[5], c[6]],
        final_message,
        openings,
    })
}
