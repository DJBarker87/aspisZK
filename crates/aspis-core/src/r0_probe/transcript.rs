//! P1 cost-probe transcript. C1 samples rows 28–29 in K.
use super::{
    domain::Point,
    opening::{self, Claims, Endpoints, Points, Roots},
    wire, Error, FinalMessage,
};
use crate::{
    field::WideExact as E,
    r0_transcript::{self as rb, CircleRow},
    HashFn,
};
use alloc::vec::Vec;

pub const DOMAIN: &[u8] = b"aspis:r0:20261009:v1";
#[derive(Clone)]
struct Duplex {
    hash: HashFn,
    state: [u8; 32],
    next: u8,
}
impl Duplex {
    fn absorb(&mut self, row: u8, tag: u8, payload: &[u8]) -> Result<[u8; 32], Error> {
        if self.next != row || row > 31 {
            return Err(Error::Schedule);
        }
        let len = u32::try_from(payload.len())
            .map_err(|_| Error::WrongLength)?
            .to_le_bytes();
        let state = (self.hash)(&[&self.state, &[0, 0xa0 + row], &[tag], &len, payload]);
        self.next += 1;
        Ok(state)
    }
    fn block(&mut self, row: u8, tag: u8, payload: &[u8]) -> Result<[u8; 32], Error> {
        let s = self.absorb(row, tag, payload)?;
        let block = (self.hash)(&[&s, &[1]]);
        self.state = (self.hash)(&[&s, &[2]]);
        Ok(block)
    }
}
fn fields(values: impl IntoIterator<Item = E>, count: usize) -> Result<Vec<u8>, Error> {
    let mut bytes = Vec::new();
    bytes
        .try_reserve_exact(count * 32)
        .map_err(|_| Error::Allocation)?;
    for v in values {
        bytes.extend_from_slice(&v.to_le_bytes());
    }
    Ok(bytes)
}
/// P1 transcript plumbing for the retained semantic phase. This type does
/// not verify the semantic relations; its consumer must do so before finish.
pub struct SemanticTranscript {
    duplex: Duplex,
    roots: Roots,
    challenges: [E; 25],
}
pub enum SemanticMessage<'a> {
    None,
    C2Root([u8; 32]),
    MaskSum(E),
    RoundPolynomial(&'a [E; 28]),
}
impl SemanticTranscript {
    /// public_bytes must be the existing semantic phase's canonical §9
    /// R0P.Public encoding. This opening module does not parse that statement.
    pub fn new(hash: HashFn, public_bytes: &[u8], c1: [u8; 32]) -> Result<Self, Error> {
        let len = u32::try_from(public_bytes.len())
            .map_err(|_| Error::WrongLength)?
            .to_le_bytes();
        let state = hash(&[DOMAIN, &[0], &len, public_bytes, &c1]);
        Ok(Self {
            duplex: Duplex {
                hash,
                state,
                next: 0,
            },
            roots: [c1, [0; 32]],
            challenges: [E::ZERO; 25],
        })
    }
    pub fn sample(&mut self, message: SemanticMessage<'_>) -> Result<E, Error> {
        let row = self.duplex.next;
        let (tag, payload) = match (row, message) {
            (0 | 1 | 3..=13, SemanticMessage::None) => (0, Vec::new()),
            (2, SemanticMessage::C2Root(root)) => {
                let mut p = Vec::new();
                p.try_reserve_exact(32).map_err(|_| Error::Allocation)?;
                p.extend_from_slice(&root);
                self.roots[1] = root;
                (1, p)
            }
            (14, SemanticMessage::MaskSum(v)) => (3, fields([v], 1)?),
            (15..=24, SemanticMessage::RoundPolynomial(h)) => (2, fields(h.iter().copied(), 28)?),
            _ => return Err(Error::Schedule),
        };
        let challenge = E::from_qm31(rb::qm31_sample(&self.duplex.block(row, tag, &payload)?));
        self.challenges[row as usize] = challenge;
        Ok(challenge)
    }
    pub fn state(&self) -> [u8; 32] {
        self.duplex.state
    }
    pub fn challenges(&self) -> &[E; 25] {
        &self.challenges
    }
    /// Hook where the semantic verifier hands off its acceptance result,
    /// 87 claims, challenge history, and already transcript-bound roots.
    pub fn finish(
        self,
        claims: Claims,
        semantic_accepted: bool,
    ) -> Result<SemanticBoundary, Error> {
        if self.duplex.next != 25 {
            return Err(Error::Schedule);
        }
        SemanticBoundary::from_verified_parts(
            self.duplex.state,
            self.roots,
            self.challenges,
            claims,
            semantic_accepted,
        )
    }
}
/// Trusted semantic-verifier output, NOT proof data. Construct only after
/// rows 0–24 have been checked and the state binds these exact two roots.
/// Opening verification proves no semantic relation on its own.
#[derive(Clone, Debug)]
pub struct SemanticBoundary {
    state: [u8; 32],
    roots: Roots,
    challenges: [E; 25],
    pub claims: Claims,
}
impl SemanticBoundary {
    pub fn from_verified_parts(
        state: [u8; 32],
        roots: Roots,
        challenges: [E; 25],
        claims: Claims,
        semantic_accepted: bool,
    ) -> Result<Self, Error> {
        if !semantic_accepted {
            return Err(Error::Semantic);
        }
        if challenges
            .iter()
            .any(|c| c.c1() != crate::field::QM31::ZERO)
        {
            return Err(Error::WrongField);
        }
        Ok(Self {
            state,
            roots,
            challenges,
            claims,
        })
    }
    pub fn boxed_from_verified_parts(
        state: [u8; 32],
        roots: Roots,
        challenges: &[E; 25],
        claims: &Claims,
        semantic_accepted: bool,
    ) -> Result<alloc::boxed::Box<Self>, Error> {
        if !semantic_accepted {
            return Err(Error::Semantic);
        }
        if challenges
            .iter()
            .any(|c| c.c1() != crate::field::QM31::ZERO)
        {
            return Err(Error::WrongField);
        }
        let mut out = super::heap::uninit::<Self>()?;
        // Every member is initialized before assume_init. Array copies go
        // directly to their final heap address; no full Self temporary.
        unsafe {
            let p = out.as_mut_ptr();
            core::ptr::addr_of_mut!((*p).state).write(state);
            core::ptr::addr_of_mut!((*p).roots).write(roots);
            core::ptr::addr_of_mut!((*p).challenges).copy_from_nonoverlapping(challenges, 1);
            core::ptr::addr_of_mut!((*p).claims).copy_from_nonoverlapping(claims, 1);
            Ok(out.assume_init())
        }
    }
    pub fn state(&self) -> [u8; 32] {
        self.state
    }
    pub fn roots(&self) -> Roots {
        self.roots
    }
    pub fn challenges(&self) -> &[E; 25] {
        &self.challenges
    }
    pub fn points(&self) -> Points {
        opening::points_from_alphas(&core::array::from_fn(|j| self.challenges[15 + j]))
    }
}
/// Private construction guarantees 22 distinct in-range sampler results.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct QuerySet([u32; 22]);
impl QuerySet {
    pub fn ordered(&self) -> &[u32; 22] {
        &self.0
    }
    pub fn sorted(&self) -> [u32; 22] {
        let mut s = self.0;
        s.sort_unstable();
        s
    }
}
pub struct OpeningTranscript {
    duplex: Duplex,
}
impl OpeningTranscript {
    pub fn new(hash: HashFn, boundary: &SemanticBoundary) -> Self {
        Self {
            duplex: Duplex {
                hash,
                state: boundary.state,
                next: 25,
            },
        }
    }
    pub fn state(&self) -> [u8; 32] {
        self.duplex.state
    }
    pub fn z0(&mut self, claims: &Claims) -> Result<Point<E>, Error> {
        let block = self
            .duplex
            .block(25, 4, &fields(claims.iter().flatten().copied(), 87)?)?;
        let p = rb::circle_sample(&block, CircleRow::First);
        Ok(Point {
            x: E::from_qm31(p.x),
            y: E::from_qm31(p.y),
        })
    }
    pub fn z1(&mut self, y0: &[E; 29]) -> Result<Point<E>, Error> {
        let block = self.duplex.block(26, 5, &fields(y0.iter().copied(), 29)?)?;
        let p = rb::circle_sample(&block, CircleRow::Second);
        Ok(Point {
            x: E::from_qm31(p.x),
            y: E::from_qm31(p.y),
        })
    }
    pub fn gamma(&mut self, y: &Endpoints) -> Result<E, Error> {
        let g = rb::gamma_sample(&self.duplex.block(
            27,
            6,
            &fields(y.iter().flatten().copied(), 58)?,
        )?);
        if g == E::ZERO {
            return Err(Error::Sampler);
        }
        Ok(g)
    }
    pub fn kappa(&mut self, v: E) -> Result<E, Error> {
        Ok(E::from_qm31(rb::qm31_sample(&self.duplex.block(
            28,
            7,
            &v.to_le_bytes(),
        )?)))
    }
    pub fn tau(&mut self) -> Result<E, Error> {
        Ok(E::from_qm31(rb::qm31_sample(&self.duplex.block(
            29,
            8,
            &[],
        )?)))
    }
    /// Full seven reconstructed coefficients, not the six proof-wire fields.
    pub fn alpha(&mut self, c: &[E; 7]) -> Result<E, Error> {
        Ok(rb::ordinary_sample(&self.duplex.block(
            30,
            9,
            &fields(c.iter().copied(), 7)?,
        )?))
    }
    pub fn queries(&mut self, f: &FinalMessage<E>) -> Result<QuerySet, Error> {
        // F is absorbed once before EVERY pair, including unselected pairs.
        self.queries_canonical_bytes(&fields(f.iter().copied(), 256)?)
    }
    /// Canonical field bytes, already validated by OpeningView. Same row-31
    /// absorb and sampler as the owned proof path, without a final array.
    pub(crate) fn queries_canonical_bytes(&mut self, bytes: &[u8]) -> Result<QuerySet, Error> {
        let mut state = self.duplex.absorb(31, 10, bytes)?;
        let mut blocks = [[0u8; 32]; 8];
        let mut advances = blocks;
        for k in 0..8 {
            blocks[k] = (self.duplex.hash)(&[&state, &[1]]);
            advances[k] = (self.duplex.hash)(&[&state, &[2]]);
            state = advances[k];
        }
        let (s, returned) =
            rb::queries_from_pairs(&blocks, &advances).map_err(|_| Error::Sampler)?;
        self.duplex.state = returned;
        Ok(QuerySet(s))
    }
}
// Keep framing helpers private to this profile; no legacy Transcript labels
// or state transitions are changed by P1.
const _: usize = wire::E_BYTES;
