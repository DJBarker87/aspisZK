#![no_std]
extern crate alloc;
extern crate self as aspis_core;
/// hashv-shaped backend: hash the concatenation of the input slices.
pub type HashFn = fn(&[&[u8]]) -> [u8; 32];
pub mod field {
/// The Mersenne prime 2^31 - 1.
pub const P: u32 = 0x7fff_ffff;
/// M31 base field element, canonical representation in [0, P).
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct M31(pub u32);
/// CM31 = M31[i] / (i^2 + 1). Element a + b*i.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct CM31 {
    pub a: M31,
    pub b: M31,
}
/// QM31 = CM31[u] / (u^2 - (2 + i)). Element c0 + c1*u. (stwo parameterization)
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct QM31 {
    pub c0: CM31,
    pub c1: CM31,
}
impl QM31 {
    pub const ZERO: QM31 = QM31 {
        c0: CM31 {
            a: M31(0),
            b: M31(0),
        },
        c1: CM31 {
            a: M31(0),
            b: M31(0),
        },
    };
}
pub mod wide_exact { use super::{M31,CM31,QM31,P};
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
#[inline(always)]
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
impl WideExact {
    /// The field embedding `x -> x + 0*v`; canonicalizes raw QM31 limbs.
    #[inline(always)]
    pub fn from_qm31(value: QM31) -> Self {
        Self {
            c0: canonical_qm31(value),
            c1: QM31::ZERO,
        }
    }
}}
pub use wide_exact::WideExact;
}
pub mod r0 {
pub const MESSAGE_LEN: usize = 1024;
pub type Message<E> = [E; MESSAGE_LEN];
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    IndexOutOfRange,
    WrongLength,
    ZeroDenominator,
    Allocation,
    NonCanonical,
    WrongField,
    InvalidPoints,
    QuotientNotInImage,
    RankDeficient,
    Parse,
    Semantic,
    Schedule,
    Sampler,
    Commitment,
    Authentication,
    V1,
    V2,
}
pub mod domain {
/// Coordinates over F, K or E. Construction itself does not assert circle
/// membership or the non-base/distinct hypotheses of the chord theorem.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Point<E> {
    pub x: E,
    pub y: E,
}
}
pub mod merkle {use alloc::vec::Vec;
pub type Digest = [u8; 32];
/// Complete six-level tree, exactly 8^6 fibres. Retained for opening paths.
pub struct Tree {
    levels: Vec<Vec<Digest>>,
}
impl Tree {pub fn root(&self)->Digest {unreachable!()}} }
}
pub mod transport {
//! UNPROVED COST PROBE. S uses the D18 digit permutation; D uses retained D13.
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub enum Variant { S1, S2, D }
}
pub mod r1_wire {
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    Allocation,
    RowOrder { expected: u8, actual: u8 },
    InvalidRow,
    Tag { row: u8 },
    Length { row: u8 },
    NonCanonical { row: u8, value: usize },
    Boundary { round: usize },
    Terminal,
    EqualCirclePoints,
    TrailingBytes,
    Public,
}
}
pub mod host_semantic { use crate::{field::{M31,QM31},r1_wire::Error};
    #[derive(Clone, Copy)]
    pub enum Column<'a> {
        Base(&'a [M31; 1024]),
        Extension(&'a [QM31; 1024]),
    }
    /// Backend errors cause an abort, never a retry or a challenge filter.
    pub trait Commitments {
        fn c1(&mut self, columns: [Column<'_>; 27]) -> Result<[u8; 32], Error>;
        fn c2(&mut self, columns: [&[QM31; 1024]; 2]) -> Result<[u8; 32], Error>;
    }
}
pub mod host_commitment {use alloc::vec::Vec; use crate::{HashFn,field::{WideExact as E,M31,QM31},r0::{domain::Point,merkle::Tree,Error,Message}};
/// Natural-product evaluation tree. Coordinates are always in F.
pub struct EncodingDomain {
    xy: Vec<Point<M31>>,
    levels: Vec<Vec<M31>>,
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
/// C1 can be constructed before λ/χ; C2 separately after them. The 29-entry
/// input permits virtual lanes but only this time's lanes are committed.
pub struct Commitment {
    time: CommitmentTime,
    lanes: Vec<usize>,
    messages: Vec<Message<E>>,
    words: Vec<Word>,
    tree: Tree,
    private_salts: Option<PrivateSalts>,
}
/// Host-only secret salts retained until queried openings have been emitted.
/// Drop overwrites the full salt buffer so salts for unopened leaves are not
/// left in the allocator after proof construction.
pub struct PrivateSalts(Vec<[u8; 32]>);
impl Commitment {
    pub fn new(
        hash: HashFn,
        domain: &EncodingDomain,
        time: CommitmentTime,
        messages: &[Message<E>],
        variant: crate::transport::Variant,
    ) -> Result<Self, Error> {
        Self::build(hash, domain, time, messages, variant, None)
    }
    pub fn new_salted(
        hash: HashFn,
        domain: &EncodingDomain,
        time: CommitmentTime,
        messages: &[Message<E>],
        variant: crate::transport::Variant,
        salts: PrivateSalts,
    ) -> Result<Self, Error> {
        Self::build(hash, domain, time, messages, variant, Some(salts))
    }
    pub fn root(&self) -> [u8; 32] {
        self.tree.root()
    }
fn build(_:HashFn,_:&EncodingDomain,_:CommitmentTime,_:&[Message<E>],_:crate::transport::Variant,_:Option<PrivateSalts>)->Result<Self,Error>{unreachable!()}
}}
pub mod prover {use alloc::vec::Vec;use crate::{HashFn,field::{WideExact as E,QM31 as K},r0::Message,transport::Variant,host_commitment::{Commitment,CommitmentTime,EncodingDomain},host_semantic::{Column,Commitments},r1_wire::Error as SError};
fn copy_c2_columns(messages:&mut Vec<Message<E>>,columns:[&[K;1024];2]) {for (i,c) in columns.into_iter().enumerate(){messages[26+i]=c.map(E::from_qm31);}}
pub struct Backend {pub hash:HashFn,pub variant:Variant,pub domain:EncodingDomain,pub messages:Vec<Message<E>>,pub c1:Option<Commitment>,pub c2:Option<Commitment>,c1_salts:Option<crate::host_commitment::PrivateSalts>,c2_salts:Option<crate::host_commitment::PrivateSalts>}
impl Commitments for Backend {fn c1(&mut self,_:[Column<'_>;27])->Result<[u8;32],SError>{unreachable!()}
    fn c2(&mut self,columns:[&[K;1024];2])->Result<[u8;32],SError>{
        copy_c2_columns(&mut self.messages,columns);
        let c=if let Some(salts)=self.c2_salts.take(){Commitment::new_salted(self.hash,&self.domain,CommitmentTime::C2,&self.messages,self.variant,salts)}else{Commitment::new(self.hash,&self.domain,CommitmentTime::C2,&self.messages,self.variant)}.map_err(|_|SError::Public)?;
        let root=c.root();self.c2=Some(c);Ok(root)
    }
}}
pub fn c2_entry(backend:&mut prover::Backend,columns:[&[field::QM31;1024];2])->Result<[u8;32],r1_wire::Error> {host_semantic::Commitments::c2(backend,columns)}
