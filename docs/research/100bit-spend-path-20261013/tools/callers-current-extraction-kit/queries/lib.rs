// Source-preserving module layout for extraction-tool input review.
// Every declaration body is included unchanged from its recorded fragment.
// This layout is not compiled as part of kit generation.
extern crate alloc;

pub mod aspis_core {
 pub mod transcript { /// Failure of bounded exact-uniform query sampling without replacement.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum QuerySampleError {
    /// Masking is exact only when the domain size is a nonzero power of two.
    BoundNotPowerOfTwo { bound: u32 },
    /// A without-replacement sample cannot contain more points than its domain.
    CountExceedsBound { count: usize, bound: u32 },
    /// The configured candidate-draw cap was reached before `count` distinct
    /// positions were accepted. This is an explicit completeness abort.
    DrawLimitExhausted { accepted: usize, max_draws: usize },
} }
 pub mod r0_transcript {pub fn queries_from_pairs(_: &[[u8;32];8],_: &[[u8;32];8])->Result<([u32;22],[u8;32]),super::transcript::QuerySampleError>{unreachable!()} }
pub trait Digest32: Copy {
    fn digest(&self, parts: &[&[u8]]) -> [u8; 32];
}
    pub mod field {
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
 impl WideExact {pub fn from_m31(_:M31)->Self {unreachable!()}}
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
        impl CM31 {
    #[inline(always)]
    pub fn new(a: M31, b: M31) -> CM31 {
        CM31 { a, b }
    }
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
/// The Mersenne prime 2^31 - 1.
pub const P: u32 = 0x7fff_ffff;
/// M31 base field element, canonical representation in [0, P).
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct M31(pub u32);
    }
    pub mod state_only_prefix {
        #[cfg(feature = "r0")]
        pub mod r0 {
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
    }
}

pub mod poseidon2 {
    use crate::aspis_core::field::M31;
pub const DIGEST_ELEMS: usize = 8;
pub type Digest = [M31; DIGEST_ELEMS];
}

pub mod pool_v1 {
    pub mod format {
pub const POOL_V1_TREE_DEPTH: usize = 20;
    }
    pub use format::POOL_V1_TREE_DEPTH;

    pub mod pair_terminal {
        use crate::poseidon2::Digest;
/// Minimal proof-carried append result for the one-terminal transaction.
///
/// This is not the execution-time append experiment above.  The selected
/// verifier has checked the twenty late Poseidon parents against the exact
/// live snapshot and returns the resulting state.  The Pool performs only
/// canonical byte validation, checks `next_pair_index = current + 1`, and
/// persists these bytes atomically with history and the nullifier marker.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1PairVerifiedAfterstateV1 {
    pub next_pair_index: u64,
    pub next_root: Digest,
    pub next_frontier: [Digest; super::POOL_V1_PAIR_TREE_DEPTH],
}
    }
    pub use pair_terminal::PoolV1PairVerifiedAfterstateV1;

    pub mod pair_tree_profile {
        use crate::poseidon2::Digest;
        use super::{PoolV1PairVerifiedAfterstateV1, POOL_V1_TREE_DEPTH};
pub const POOL_V1_PAIR_TREE_DEPTH: usize = POOL_V1_TREE_DEPTH;
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1PairLiveSnapshotV1 {
    pub pool: [u8; 32],
    pub deployment_domain: [u8; 32],
    pub sequence: u64,
    pub next_pair_index: u64,
    pub current_root: Digest,
    pub frontier: [Digest; POOL_V1_PAIR_TREE_DEPTH],
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1PairLatePublicStatementV1 {
    pub live_snapshot: PoolV1PairLiveSnapshotV1,
    /// One appended pair advances the pair index by one even though a private
    /// transfer fills two commitment slots (note indices `2i` and `2i+1`).
    pub candidate_afterstate: PoolV1PairVerifiedAfterstateV1,
}
    }
    pub use pair_tree_profile::POOL_V1_PAIR_TREE_DEPTH;

    pub mod payment_relation {
        use crate::aspis_core::field::M31;
        use crate::poseidon2::Digest;
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1PrivateTransferPublicV1 {
    pub pool: [u8; 32],
    pub deployment_domain: [u8; 32],
    pub anchor_sequence: u64,
    pub anchor_root: Digest,
    pub nullifier: Digest,
    pub asset_id: M31,
    pub recipient_commitment: Digest,
    pub change_commitment: Digest,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1WithdrawalPublicV1 {
    pub pool: [u8; 32],
    pub deployment_domain: [u8; 32],
    pub anchor_sequence: u64,
    pub anchor_root: Digest,
    pub nullifier: Digest,
    pub asset_id: M31,
    pub amount: u32,
    pub destination_token_account: [u8; 32],
    pub change_commitment: Digest,
}
    }

    pub mod pair_forest_terminal {
        use crate::poseidon2::Digest;
        use super::pair_tree_profile::PoolV1PairLatePublicStatementV1;
        use super::payment_relation::{PoolV1PrivateTransferPublicV1, PoolV1WithdrawalPublicV1};
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1PairForestTerminalCommonV1 {
    pub master_account: [u8; 32],
    pub checkpoint_account: [u8; 32],
    pub selected_lane_account: [u8; 32],
    pub output_lane: u8,
    pub checkpoint_sequence: u64,
    /// Historical global membership anchor reconstructed at trace block 56.
    pub historical_global_anchor: Digest,
    /// Exact selected-output-lane beforestate and candidate afterstate.
    pub lane_transition: PoolV1PairLatePublicStatementV1,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1PairForestTerminalStatementV1 {
    PrivateTransfer {
        common: PoolV1PairForestTerminalCommonV1,
        public: PoolV1PrivateTransferPublicV1,
    },
    Withdrawal {
        common: PoolV1PairForestTerminalCommonV1,
        public: PoolV1WithdrawalPublicV1,
    },
}
        impl PoolV1PairForestTerminalStatementV1 {
    #[cfg(feature = "r0")]
    #[inline(always)]
    pub fn semantic_public(&self) -> super::pair_forest_semantic_terminal::r0::Public<'_> {
        use super::pair_forest_semantic_terminal::r0::Public;
        match self {
            Self::PrivateTransfer { common, public } => {
                Public::Transfer(public, &common.lane_transition)
            }
            Self::Withdrawal { common, public } => {
                Public::Withdrawal(public, &common.lane_transition)
            }
        }
    }
        }
    }

    pub mod pair_forest_semantic_terminal {
        use crate::aspis_core::field::M31;
        use crate::poseidon2::Digest;
        use super::{
            pair_tree_profile::PoolV1PairLatePublicStatementV1,
            payment_relation::{PoolV1PrivateTransferPublicV1, PoolV1WithdrawalPublicV1},
        };

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CompiledVariant {
    PrivateTransfer,
    Withdrawal,
}
#[derive(Clone, Copy)]
struct SemanticPublic<'a> {
    variant: CompiledVariant,
    pool: [u8; 32],
    deployment_domain: [u8; 32],
    anchor: Digest,
    nullifier: Digest,
    asset_id: M31,
    recipient: Option<Digest>,
    change: Digest,
    withdrawal_amount: Option<u32>,
    transition: &'a PoolV1PairLatePublicStatementV1,
}
fn private_public<'a>(
    public: &PoolV1PrivateTransferPublicV1,
    transition: &'a PoolV1PairLatePublicStatementV1,
) -> SemanticPublic<'a> {
    SemanticPublic {
        variant: CompiledVariant::PrivateTransfer,
        pool: public.pool,
        deployment_domain: public.deployment_domain,
        anchor: public.anchor_root,
        nullifier: public.nullifier,
        asset_id: public.asset_id,
        recipient: Some(public.recipient_commitment),
        change: public.change_commitment,
        withdrawal_amount: None,
        transition,
    }
}
fn withdrawal_public<'a>(
    public: &PoolV1WithdrawalPublicV1,
    transition: &'a PoolV1PairLatePublicStatementV1,
) -> SemanticPublic<'a> {
    SemanticPublic {
        variant: CompiledVariant::Withdrawal,
        pool: public.pool,
        deployment_domain: public.deployment_domain,
        anchor: public.anchor_root,
        nullifier: public.nullifier,
        asset_id: public.asset_id,
        recipient: None,
        change: public.change_commitment,
        withdrawal_amount: Some(public.amount),
        transition,
    }
}

        #[cfg(feature = "r0")]
        pub mod r0 {
            use alloc::vec::Vec;
            use crate::aspis_core;
            use crate::aspis_core::{field::{M31, P}, state_only_prefix::r0::Error};
            use super::*;
    #[derive(Clone, Copy)]
    pub enum Public<'a> {
        Transfer(
            &'a PoolV1PrivateTransferPublicV1,
            &'a PoolV1PairLatePublicStatementV1,
        ),
        Withdrawal(
            &'a PoolV1WithdrawalPublicV1,
            &'a PoolV1PairLatePublicStatementV1,
        ),
    }
            impl<'a> Public<'a> {
        fn semantic(self) -> SemanticPublic<'a> {
            match self {
                Self::Transfer(public, transition) => private_public(public, transition),
                Self::Withdrawal(public, transition) => withdrawal_public(public, transition),
            }
        }
        /// SPEC §9 declaration order. Pool/domain/sequence and source current
        /// root are not fields of R0P.Public and are not silently hashed here.
        /// Existing reject-only public guards remain in the terminal.
        pub fn public_bytes(self) -> Result<Vec<u8>, Error> {
            fn fields(out: &mut Vec<u8>, values: &[M31]) -> Result<(), Error> {
                for value in values {
                    if value.0 >= aspis_core::field::P {
                        return Err(Error::Public);
                    }
                    out.extend_from_slice(&value.0.to_le_bytes());
                }
                Ok(())
            }
            // The fixed width is checked at both call sites. Explicit calls
            // avoid nested frontier loops during source extraction.
            fn frontier(out: &mut Vec<u8>, values: &[Digest; 20]) -> Result<(), Error> {
                fields(out, &values[0])?;
                fields(out, &values[1])?;
                fields(out, &values[2])?;
                fields(out, &values[3])?;
                fields(out, &values[4])?;
                fields(out, &values[5])?;
                fields(out, &values[6])?;
                fields(out, &values[7])?;
                fields(out, &values[8])?;
                fields(out, &values[9])?;
                fields(out, &values[10])?;
                fields(out, &values[11])?;
                fields(out, &values[12])?;
                fields(out, &values[13])?;
                fields(out, &values[14])?;
                fields(out, &values[15])?;
                fields(out, &values[16])?;
                fields(out, &values[17])?;
                fields(out, &values[18])?;
                fields(out, &values[19])?;
                Ok(())
            }
            let p = self.semantic();
            let mut out = Vec::new();
            out.push(match p.variant {
                CompiledVariant::PrivateTransfer => 0,
                CompiledVariant::Withdrawal => 1,
            });
            fields(&mut out, &p.anchor)?;
            fields(&mut out, &p.nullifier)?;
            fields(&mut out, &[p.asset_id])?;
            out.push(u8::from(p.recipient.is_some()));
            if let Some(value) = p.recipient {
                fields(&mut out, &value)?;
            }
            fields(&mut out, &p.change)?;
            out.push(u8::from(p.withdrawal_amount.is_some()));
            if let Some(value) = p.withdrawal_amount {
                fields(&mut out, &[M31(value)])?;
            }
            let source = p.transition.live_snapshot;
            let after = p.transition.candidate_afterstate;
            out.extend_from_slice(&source.next_pair_index.to_le_bytes());
            frontier(&mut out, &source.frontier)?;
            fields(&mut out, &after.next_root)?;
            frontier(&mut out, &after.next_frontier)?;
            Ok(out)
        }
            }
        }
    }
}

pub mod sampler {
 use crate::aspis_core::field::{CM31,M31,P,QM31};
/// Divide a little-endian word array by P, retaining every quotient word.
/// Dividends are below P * 2^32, so every division fits in u64.
fn qm31_div_pass(mut rank: [u32; 8]) -> ([u32; 8], u32) {
    let mut remainder = 0u64;
    let mut j = 8usize;
    while j > 0 {
        j -= 1;
        let dividend = (remainder << 32) | u64::from(rank[j]);
        rank[j] = (dividend / u64::from(P)) as u32;
        remainder = dividend % u64::from(P);
    }
    (rank, remainder as u32)
}
/// The low four base-P digits already represent rank modulo P^4.
fn qm31_digits(block: &[u8; 32]) -> [u32; 4] {
    let mut rank = [0u32; 8];
    let mut i = 0usize;
    while i < 8 {
        let start = 4 * i;
        rank[i] = u32::from_le_bytes([
            block[start],
            block[start + 1],
            block[start + 2],
            block[start + 3],
        ]);
        i += 1;
    }
    let mut digits = [0u32; 4];
    let mut i = 0usize;
    while i < 4 {
        let (quotient, digit) = qm31_div_pass(rank);
        rank = quotient;
        digits[i] = digit;
        i += 1;
    }
    digits
}
pub fn qm31_sample(block: &[u8; 32]) -> QM31 {
    let digits = qm31_digits(block);
    QM31 {
        c0: CM31::new(M31(digits[0]), M31(digits[1])),
        c1: CM31::new(M31(digits[2]), M31(digits[3])),
    }
}
}
pub mod r1_wire {
 use crate::aspis_core::field::QM31;
 use crate::sampler::qm31_sample;
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct Challenges {
        pub lambda: QM31,
        pub chi: QM31,
        pub theta: QM31,
        pub zc: [QM31; 10],
        pub mu: QM31,
        pub eta: QM31,
    }
/// A record whose framing and every field limb were checked by
/// `parse_record`. Tokens are issued only from a successfully parsed Prefix;
/// callers cannot supply a row separately from its bytes.
#[derive(Clone, Copy)]
pub(crate) struct ValidatedRecord<'a> {
    row: u8,
    framed: &'a [u8],
}
 impl<'a> ValidatedRecord<'a> {
    pub(crate) fn row(&self) -> u8 {
        self.row
    }
    pub(crate) fn framed(&self) -> &'a [u8] {
        self.framed
    }
 }
/// Compact semantic wire: C1 root, followed by the 27 P1 records through
/// beforeZ1. No header, mask nonce, work nonce or opening suffix is read.
/// The opening owner consumes the returned row-27 state and both claims.
pub struct Prefix<'a> {
    pub c1_root: &'a [u8; 32],
    records: [&'a [u8]; 27],
}
 impl<'a> Prefix<'a> {
    pub fn record(&self, row: u8) -> Result<&'a [u8], Error> {
        if row >= 27 {
            return Err(Error::InvalidRow);
        }
        Ok(self.records[row as usize])
    }
    pub(crate) fn validated_record(&self, row: u8) -> Result<ValidatedRecord<'a>, Error> {
        Ok(ValidatedRecord {
            row,
            framed: self.record(row)?,
        })
    }
 }
/// Rows 0..14. Roots are the only commitment records; there is no helper
/// zero-sum/registry absorb between row 2 and theta.
#[inline(never)]
pub fn begin<H: Digest32>(
    prefix: &Prefix<'_>,
    transcript: &mut SemanticTranscript<H>,
) -> Result<Challenges, Error> {
    let lambda = transcript.semantic_validated(prefix.validated_record(0)?)?;
    let chi = transcript.semantic_validated(prefix.validated_record(1)?)?;
    let theta = transcript.semantic_validated(prefix.validated_record(2)?)?;
    let mut zc = [QM31::ZERO; 10];
    zc[0] = transcript.semantic_validated(prefix.validated_record(3)?)?;
    zc[1] = transcript.semantic_validated(prefix.validated_record(4)?)?;
    zc[2] = transcript.semantic_validated(prefix.validated_record(5)?)?;
    zc[3] = transcript.semantic_validated(prefix.validated_record(6)?)?;
    zc[4] = transcript.semantic_validated(prefix.validated_record(7)?)?;
    zc[5] = transcript.semantic_validated(prefix.validated_record(8)?)?;
    zc[6] = transcript.semantic_validated(prefix.validated_record(9)?)?;
    zc[7] = transcript.semantic_validated(prefix.validated_record(10)?)?;
    zc[8] = transcript.semantic_validated(prefix.validated_record(11)?)?;
    zc[9] = transcript.semantic_validated(prefix.validated_record(12)?)?;
    let mu = transcript.semantic_validated(prefix.validated_record(13)?)?;
    let eta = transcript.semantic_validated(prefix.validated_record(14)?)?;
    Ok(Challenges {
        lambda,
        chi,
        theta,
        zc,
        mu,
        eta,
    })
}
    use crate::aspis_core::Digest32;
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
#[cfg(not(feature = "private-leaf-salts"))]
pub const DOMAIN: &[u8] = b"aspis:r0:20261009:v1";
#[cfg(feature = "private-leaf-salts")]
pub const DOMAIN: &[u8] = b"UNPROVED:R1:PRIVATE-SALTED:SEMANTIC:P3";
/// Fresh R0 state, separate from Transcript's legacy all-zero IV. The
/// C1-time binding is exactly SPEC §9: public bytes and the C1 root in one
/// hash, with no profile/basis/nonce/registry pre-absorbs. Row 0 is empty.
#[derive(Clone)]
pub struct SemanticTranscript<H: Digest32> {
    state: [u8; 32],
    hash: H,
    next_row: u8,
}
    impl<H: Digest32> SemanticTranscript<H> {
    pub fn new(hash: H, public_bytes: &[u8], c1_root: &[u8; 32]) -> Result<Self, Error> {
        let length = u32::try_from(public_bytes.len()).map_err(|_| Error::Public)?;
        Ok(Self {
            state: hash.digest(&[DOMAIN, &[0], &length.to_le_bytes(), public_bytes, c1_root]),
            hash,
            next_row: 0,
        })
    }
    fn sample_block_validated(&mut self, row: u8, framed: &[u8]) -> Result<[u8; 32], Error> {
        if row != self.next_row {
            return Err(Error::RowOrder {
                expected: self.next_row,
                actual: row,
            });
        }
        // Exactly one absorb, one squeeze and one advance. Both reads
        // use s_abs; advancing from the challenge block would be wrong.
        let absorbed = self.hash.digest(&[&self.state, &[0, 0xa0 + row], framed]);
        let block = self.hash.digest(&[&absorbed, &[1]]);
        self.state = self.hash.digest(&[&absorbed, &[2]]);
        self.next_row += 1;
        Ok(block)
    }
    pub(crate) fn semantic_validated(
        &mut self,
        record: ValidatedRecord<'_>,
    ) -> Result<QM31, Error> {
        let row = record.row();
        if row > 24 {
            return Err(Error::InvalidRow);
        }
        Ok(qm31_sample(
            &self.sample_block_validated(row, record.framed())?,
        ))
    }
    }
    pub fn semantic_validated_entry<H: Digest32>(transcript: &mut SemanticTranscript<H>, record: ValidatedRecord<'_>) -> Result<QM31, Error> { transcript.semantic_validated(record) }
    pub fn prefix_validated_entry<'a>(prefix: &Prefix<'a>, row: u8) -> Result<ValidatedRecord<'a>, Error> { prefix.validated_record(row) }
    // Extraction-only entry wrapper: actual private method body is unchanged.
    pub fn sample_validated_entry<H: Digest32>(
        transcript: &mut SemanticTranscript<H>, row: u8, framed: &[u8],
    ) -> Result<[u8; 32], Error> {
        transcript.sample_block_validated(row, framed)
    }
}

pub mod r1_semantic {
    use crate::aspis_core::Digest32;
    use crate::r1_wire::{Error, SemanticTranscript};
    use crate::pool_v1::pair_forest_semantic_terminal::r0::Public;
#[inline(always)]
pub fn public_transcript<H: Digest32>(
    public: Public<'_>,
    hash: H,
    c1_root: &[u8; 32],
) -> Result<SemanticTranscript<H>, Error> {
    SemanticTranscript::new(
        hash,
        &public.public_bytes().map_err(|_| Error::Public)?,
        c1_root,
    )
}
}

pub mod transport {
//! UNPROVED COST PROBE. S uses the D18 digit permutation; D uses retained D13.
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub enum Variant { S1, S2, D }
 impl Variant {
    pub fn tag(self) -> u8 { match self { Self::S1=>1,Self::S2=>2,Self::D=>3 } }
 }
}
pub mod transcript {
 use crate::aspis_core; use crate::aspis_core::field::WideExact as E;
 use crate::aspis_core::Digest32;
 use crate::transport::Variant;
pub struct Transcript<H: Digest32> { pub state:[u8;32], hash:H }
 impl<H: Digest32> Transcript<H> {
    pub fn new(hash:H, semantic_state:[u8;32], variant:Variant) -> Self {
        #[cfg(not(feature = "private-leaf-salts"))]
        let domain: &[u8] = b"UNPROVED:R1:COST-PROBE:P2";
        #[cfg(feature = "private-leaf-salts")]
        let domain: &[u8] = b"UNPROVED:R1:PRIVATE-SALTED:P3";
        Self { state:hash.digest(&[domain,&[variant.tag()],&semantic_state]), hash }
    }
    pub fn absorb(&mut self, row:u8, payload:&[u8]) {
        self.state=self.hash.digest(&[&self.state,&[0,0xa0+row],&(payload.len() as u32).to_le_bytes(),payload]);
    }
    pub fn block(&mut self,row:u8,payload:&[u8])->[u8;32] {
        self.absorb(row,payload);
        let block=self.hash.digest(&[&self.state,&[1]]);
        self.state=self.hash.digest(&[&self.state,&[2]]);
        block
    }
 }
 impl<H:Digest32> Transcript<H> {     pub fn queries(&mut self, row:u8, payload:&[u8])->Result<[u32;22],crate::verifier::Error> {
        self.absorb(row,payload);
        let mut blocks=[[0;32];8];let mut advances=blocks; let mut state=self.state;
        blocks[0]=self.hash.digest(&[&state,&[1]]);
        advances[0]=self.hash.digest(&[&state,&[2]]);state=advances[0];
        blocks[1]=self.hash.digest(&[&state,&[1]]);
        advances[1]=self.hash.digest(&[&state,&[2]]);state=advances[1];
        blocks[2]=self.hash.digest(&[&state,&[1]]);
        advances[2]=self.hash.digest(&[&state,&[2]]);state=advances[2];
        blocks[3]=self.hash.digest(&[&state,&[1]]);
        advances[3]=self.hash.digest(&[&state,&[2]]);state=advances[3];
        blocks[4]=self.hash.digest(&[&state,&[1]]);
        advances[4]=self.hash.digest(&[&state,&[2]]);state=advances[4];
        blocks[5]=self.hash.digest(&[&state,&[1]]);
        advances[5]=self.hash.digest(&[&state,&[2]]);state=advances[5];
        blocks[6]=self.hash.digest(&[&state,&[1]]);
        advances[6]=self.hash.digest(&[&state,&[2]]);state=advances[6];
        blocks[7]=self.hash.digest(&[&state,&[1]]);
        advances[7]=self.hash.digest(&[&state,&[2]]);state=advances[7];
        let (q,state)=aspis_core::r0_transcript::queries_from_pairs(&blocks,&advances).map_err(|_|crate::verifier::Error::Transcript)?;
        self.state=state;
        { let u=q[0]; crate::trace::value(5,0,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[1]; crate::trace::value(5,1,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[2]; crate::trace::value(5,2,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[3]; crate::trace::value(5,3,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[4]; crate::trace::value(5,4,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[5]; crate::trace::value(5,5,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[6]; crate::trace::value(5,6,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[7]; crate::trace::value(5,7,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[8]; crate::trace::value(5,8,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[9]; crate::trace::value(5,9,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[10]; crate::trace::value(5,10,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[11]; crate::trace::value(5,11,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[12]; crate::trace::value(5,12,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[13]; crate::trace::value(5,13,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[14]; crate::trace::value(5,14,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[15]; crate::trace::value(5,15,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[16]; crate::trace::value(5,16,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[17]; crate::trace::value(5,17,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[18]; crate::trace::value(5,18,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[19]; crate::trace::value(5,19,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[20]; crate::trace::value(5,20,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[21]; crate::trace::value(5,21,E::from_m31(aspis_core::field::M31(u))); }
        Ok(q)
    } }

}

pub mod verifier { #[derive(Debug,Clone,Copy,PartialEq,Eq)]
pub enum Error { Parse,Semantic,Transcript,Relation,Merkle,Query,Checkpoint,Allocation } }
 pub mod trace { use crate::aspis_core::field::WideExact as E; #[inline(always)]
pub fn value(tag: u16, index: usize, x: E) {
    #[cfg(feature="prover")]
    VALUES.with(|v| v.borrow_mut().push((tag,index,x.to_le_bytes())));
    #[cfg(not(feature="prover"))]
    let _ = (tag,index,x);
} }
 pub fn queries_entry<H:crate::aspis_core::Digest32>(mut transcript:crate::transcript::Transcript<H>,row:u8,payload:&[u8])->Result<[u32;22],crate::verifier::Error>{transcript.queries(row,payload)}
