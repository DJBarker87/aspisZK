// Source-preserving module layout for extraction-tool input review.
// Every declaration body is included unchanged from its recorded fragment.
// This layout is not compiled as part of kit generation.
extern crate alloc;

pub mod aspis_core {
 pub mod circle { use super::field::QM31;
/// A point `(x, y)` on `x^2 + y^2 = 1` over QM31.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SecureCirclePoint {
    pub x: QM31,
    pub y: QM31,
}
}
 pub mod state_only_hiding { use super::field::QM31; pub fn state_only_selected_mask_value(_: &[QM31;16],_: &[QM31;10],_:QM31,_:&[QM31;10])->QM31 {unreachable!()} }
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
 impl WideExact {
    pub const ZERO: Self = Self {
        c0: QM31::ZERO,
        c1: QM31::ZERO,
    };
 pub fn to_le_bytes(self)->[u8;32]{unreachable!()} pub fn c0(self)->QM31 {self.c0} pub fn from_qm31(_:QM31)->Self {unreachable!()} pub fn from_m31(_:M31)->Self {unreachable!()} pub fn add(self,_:Self)->Self {unreachable!()} pub fn mul(self,_:Self)->Self {unreachable!()} pub fn mul_m31(self,_:M31)->Self {unreachable!()} }
 impl QM31 { pub fn add(self,_:Self)->Self {unreachable!()} pub fn mul(self,_:Self)->Self {unreachable!()} }
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
 pub use crate::r1_wire::Challenges;
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
 pub fn terminal_qm31(self,_:&[[crate::aspis_core::field::QM31;29];3],_:&[crate::aspis_core::field::QM31;10],_:&crate::r1_wire::Challenges)->Result<crate::aspis_core::field::QM31,Error> {unreachable!()}
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
 use crate::aspis_core::{circle::SecureCirclePoint,field::WideExact};
/// Selects the existing row fallback: parameter u for row 25, 1+u for 26.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CircleRow {
    First,
    Second,
}
 pub fn circle_sample(_:&[u8;32],_:CircleRow)->SecureCirclePoint {unreachable!()} pub fn ordinary_sample(_:&[u8;32])->WideExact {unreachable!()} pub fn gamma_sample(_:&[u8;32])->WideExact {unreachable!()}
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
 use crate::aspis_core::circle::SecureCirclePoint; use crate::sampler::{circle_sample,CircleRow};
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
 pub(crate) fn decode_k<const N:usize>(&self,_:usize)->Result<[QM31;N],Error>{unreachable!()}
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
 pub fn parse(_:&'a[u8])->Result<Self,Error>{unreachable!()}
    pub fn payload(&self, row: u8) -> Result<&'a [u8], Error> {
        let framed = self.record(row)?;
        Ok(&framed[5..])
    }
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
    pub fn state(&self) -> [u8; 32] {
        self.state
    }
    pub(crate) fn circle_validated(
        &mut self,
        record: ValidatedRecord<'_>,
    ) -> Result<SecureCirclePoint, Error> {
        let row = record.row();
        let circle_row = match row {
            25 => CircleRow::First,
            26 => CircleRow::Second,
            _ => return Err(Error::InvalidRow),
        };
        Ok(circle_sample(
            &self.sample_block_validated(row, record.framed())?,
            circle_row,
        ))
    }
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
 use crate::aspis_core; use crate::r1_wire as wire; use alloc::boxed::Box; use crate::r1_wire::{Prefix,Challenges}; use crate::aspis_core::{circle::SecureCirclePoint,field::QM31};
pub struct Verified<H: Digest32> {
    pub roots: [[u8; 32]; 2],
    pub challenges: Challenges,
    pub alpha: [QM31; 10],
    pub claims: Box<[[QM31; 29]; 3]>,
    pub extra: [QM31; 29],
    pub before_z1: [QM31; 29],
    pub state_before_z0: [u8; 32],
    pub z: [SecureCirclePoint; 2],
    pub transcript: SemanticTranscript<H>,
    #[cfg(feature = "prover")]
    pub round_checks: [[QM31; 3]; 10],
    #[cfg(feature = "prover")]
    pub terminal: QM31,
    #[cfg(feature = "prover")]
    pub masked_terminal: QM31,
}
 fn claims(_:&Prefix)->Result<Box<[[QM31;29];3]>,Error>{unreachable!()}
#[inline(never)]
pub fn verify_observed<H: Digest32>(public: Public<'_>, bytes: &[u8], hash: H, obs: crate::verifier::Observer) -> Result<Verified<H>, Error> {
    fn mark(obs: crate::verifier::Observer, i: u8) {
        #[cfg(feature="detail-phases")]
        if let Some(f)=obs {f(crate::verifier::Phase::SemanticPart(i));}
        #[cfg(not(feature="detail-phases"))]
        let _=(obs,i);
    }
    let prefix = Prefix::parse(bytes)?;
    mark(obs, 0);
    let mut transcript = public_transcript(public, hash, prefix.c1_root)?;
    let challenges = wire::begin(&prefix, &mut transcript)?;
    mark(obs, 1);
    let mut running = prefix.validated_record(14)?.decode_k::<1>(0)?[0];
    let mut alpha = [QM31::ZERO; 10];
    #[cfg(feature = "prover")]
    let mut round_checks = [[QM31::ZERO; 3]; 10];
    for round in 0..10 {
        let row = 15 + round as u8;
        let polynomial = prefix.validated_record(row)?.decode_k::<28>(0)?;
        let boundary = polynomial.iter().copied().fold(polynomial[0], QM31::add);
        if boundary != running {
            return Err(Error::Boundary { round });
        }
        alpha[round] = transcript.semantic_validated(prefix.validated_record(row)?)?;
        let value = polynomial
            .iter()
            .rev()
            .fold(QM31::ZERO, |a, &c| a.mul(alpha[round]).add(c));
        #[cfg(feature = "prover")]
        {
            round_checks[round] = [running, boundary, value];
        }
        running = value;
    }
    mark(obs, 2);
    let claims = claims(&prefix)?;
    let original_challenges = aspis_core::state_only_prefix::r0::Challenges {
        lambda: challenges.lambda,
        chi: challenges.chi,
        theta: challenges.theta,
        zc: challenges.zc,
        mu: challenges.mu,
        eta: challenges.eta,
    };
    let terminal = public
        .terminal_qm31(&claims, &alpha, &original_challenges)
        .map_err(|_| Error::Public)?;
    mark(obs, 3);
    let mask = aspis_core::state_only_hiding::state_only_selected_mask_value(
        &core::array::from_fn(|i| claims[0][i]),
        &core::array::from_fn(|i| claims[0][16 + i]),
        claims[0][27],
        &alpha,
    );
    let extra = prefix.validated_record(25)?.decode_k::<29>(87)?;
    let masked_terminal = mask.add(challenges.eta.mul(terminal)).add(extra[28]);
    if running != masked_terminal {
        return Err(Error::Terminal);
    }
    mark(obs, 4);
    let state_before_z0 = transcript.state();
    let z0 = transcript.circle_validated(prefix.validated_record(25)?)?;
    let before_z1 = prefix.validated_record(26)?.decode_k::<29>(0)?;
    let z1 = transcript.circle_validated(prefix.validated_record(26)?)?;
    mark(obs, 5);
    #[cfg(feature = "prover")]
    {
        for (i, x) in [z0.x, z0.y, z1.x, z1.y].into_iter().enumerate() {
            crate::trace::value(3, i, aspis_core::field::WideExact::from_qm31(x));
        }
        for (i, x) in challenges.with_alphas(&alpha).into_iter().enumerate() {
            crate::trace::value(0, i, x);
        }
        for (i, row) in round_checks.iter().enumerate() {
            for (j, x) in row.iter().enumerate() {
                crate::trace::value(1, 3 * i + j, aspis_core::field::WideExact::from_qm31(*x));
            }
        }
        crate::trace::value(2, 0, aspis_core::field::WideExact::from_qm31(terminal));
        crate::trace::value(
            2,
            1,
            aspis_core::field::WideExact::from_qm31(masked_terminal),
        );
    }
    if z0 == z1 {
        return Err(Error::EqualCirclePoints);
    }
    Ok(Verified {
        roots: [*prefix.c1_root, prefix.payload(2)?.try_into().unwrap()],
        challenges,
        alpha,
        claims,
        extra,
        before_z1,
        state_before_z0,
        z: [z0, z1],
        transcript,
        #[cfg(feature = "prover")]
        round_checks,
        #[cfg(feature = "prover")]
        terminal,
        #[cfg(feature = "prover")]
        masked_terminal,
    })
}
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
    pub fn folds(self) -> usize { if self == Self::S1 { 1 } else { 2 } }
    pub fn tag(self) -> u8 { match self { Self::S1=>1,Self::S2=>2,Self::D=>3 } }
 }
}
pub mod transcript {
 use crate::aspis_core; use crate::aspis_core::field::WideExact as E;
 use crate::aspis_core::Digest32;
 use crate::transport::Variant;
pub struct Transcript<H: Digest32> { pub state:[u8;32], hash:H }
 impl<H: Digest32> Transcript<H> {
    pub fn scalar(&mut self,row:u8,payload:&[u8],nonzero:bool)->E {
        let block=self.block(row,payload);
        let out=if nonzero {crate::sampler::gamma_sample(&block)} else {crate::sampler::ordinary_sample(&block)};
        crate::trace::value(4,row as usize,out); out
    }
    /// Final query-residual batching: at most 22 coefficients, so a nonzero
    /// residual has at most 21 roots even when sampled from the K subfield.
    /// Gamma and both folding challenges continue to use E.
    pub fn scalar_k(&mut self,row:u8,payload:&[u8])->aspis_core::field::QM31 {
        let out=crate::sampler::qm31_sample(&self.block(row,payload));
        crate::trace::value(4,row as usize,E::from_qm31(out)); out
    }
 pub fn queries(&mut self,_:u8,_:&[u8])->Result<[u32;22],crate::verifier::Error> {unreachable!()}
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
}

pub mod trace {use crate::aspis_core::field::WideExact as E;
#[inline(always)]
pub fn value(tag: u16, index: usize, x: E) {
    #[cfg(feature="prover")]
    VALUES.with(|v| v.borrow_mut().push((tag,index,x.to_le_bytes())));
    #[cfg(not(feature="prover"))]
    let _ = (tag,index,x);
}
}
pub mod weights {use alloc::boxed::Box; use crate::{aspis_core::{field::{WideExact as E,QM31 as K,M31},circle::SecureCirclePoint},transport::Variant,verifier::Error};pub const QUARTER:M31=M31(536870912);
pub struct Weights {
    pub variant:Variant,
    pub factors:[[[K;4];5];5],
    pub points:[[K;10];3],
    pub extra:[K;2],
}
impl Weights {pub fn new(_:Variant,_:&[K;10],_:&[SecureCirclePoint;2])->Result<Box<Self>,Error>{unreachable!()} pub fn pair(&self,_:&[E],_:&[u8],_:E)->Result<E,Error>{unreachable!()}} pub fn powers<const N:usize>(_:E)->[E;N] {unreachable!()} pub fn field(_:&[u8],_:usize)->E {unreachable!()} }
pub mod fast_pairing {use crate::aspis_core::field::{WideExact as E,QM31}; mod canonical {    // Private canonical operands; bounded raw representatives, canonical result.
    // At most 4096 partial folds, each <2^34, sum <2^46. No u64 wrap.
    pub struct Dot { sums:[u64;4], count:usize }} /// Candidate exact accumulator for sums of `WideExact * QM31`.
/// Canonical QM31 coordinates and the 4096-term limit are checked at push.
pub struct EbyKDot {
    c0: canonical::Dot,
    c1: canonical::Dot,
    count: usize,
} impl EbyKDot {pub fn new()->Self {unreachable!()} pub fn push(&mut self,_:E,_:QM31)->Result<(),()>{unreachable!()} pub fn finish(self)->E {unreachable!()} } }
pub mod verifier {use crate::weights::{Weights,QUARTER};use alloc::{boxed::Box,vec::Vec}; use crate::{aspis_core::{Digest32,field::{WideExact as E,QM31 as K},circle::SecureCirclePoint},transport::Variant,transcript::Transcript,weights::{powers,field}};
#[derive(Debug,Clone,Copy,PartialEq,Eq)]
pub enum Error { Parse,Semantic,Transcript,Relation,Merkle,Query,Checkpoint,Allocation }
#[derive(Debug,Clone,Copy,PartialEq,Eq)]
pub enum Phase { Parsed,Semantic,SemanticPart(u8),Prepare,CheckpointRead,Merkle(usize),Query(usize),QueryPart(usize,u8),CheckpointWrite,Relation,Final }
pub type Observer=Option<fn(Phase)>;
pub struct View<'a> {
    pub variant:Variant,pub semantic:&'a[u8],pub y1:&'a[u8],pub inactive:E,
    pub round0:&'a[u8],pub folded_root:Option<&'a[u8;32]>,pub round1:&'a[u8],
    pub final_message:&'a[u8],pub query_bytes:&'a[u8],
}
pub struct Prepared {
    pub variant:Variant,pub roots:[[u8;32];2],pub gamma:E,pub kappa:E,pub alpha:[E;2],pub rho:K,
    pub queries:[u32;22],pub semantic_alpha:[K;10],pub z:[SecureCirclePoint;2],pub claim:E,pub state:[u8;32],
}

pub struct Accumulator { pub weights:Vec<K>,pub rhs:E,pub power:K,pub next:usize }
fn mark(obs:Observer,p:Phase) { if let Some(f)=obs {f(p);} }
pub fn polynomial(bytes:&[u8],x:E)->E {(0..7).rev().fold(E::ZERO,|a,i|a.mul(x).add(field(bytes,i)))}
pub fn finish_round_poly_select<'a>(round0:&'a [u8],round1:&'a [u8],round:usize)->&'a [u8] {
    if round==0 {round0}else{round1}
}

pub fn finish_round_region_cut(round0:&[u8],round1:&[u8],alpha:[E;2],variant:Variant,mut claim:E)->Result<E,Error> {
    for round in 0..variant.folds() {
        let poly=finish_round_poly_select(round0,round1,round);
        let lhs=field(poly,0).add(field(poly,4));let rhs=claim.mul_m31(QUARTER);
        crate::trace::value(15,3*round,lhs);crate::trace::value(15,3*round+1,rhs);
        if lhs!=rhs {return Err(Error::Relation);}
        claim=polynomial(poly,alpha[round]);crate::trace::value(15,3*round+2,claim);
    }
    Ok(claim)
}

#[inline(never)]
pub fn finish_relation(v:&View<'_>,p:&Prepared,a:&Accumulator,obs:Observer)->Result<(),Error> {
    let mut claim=p.claim;
    for round in 0..p.variant.folds() {
        let poly=if round==0 {v.round0}else{v.round1};
        let lhs=field(poly,0).add(field(poly,4));let rhs=claim.mul_m31(QUARTER);
        crate::trace::value(15,3*round,lhs);crate::trace::value(15,3*round+1,rhs);
        if lhs!=rhs {return Err(Error::Relation);}
        claim=polynomial(poly,p.alpha[round]);crate::trace::value(15,3*round+2,claim);
    }
    let weights=Weights::new(p.variant,&p.semantic_alpha,&p.z)?;
    let pair=weights.pair(&p.alpha[..p.variant.folds()],v.final_message,p.kappa)?;
    crate::trace::value(16,0,pair);crate::trace::value(16,1,claim);
    if pair!=claim {return Err(Error::Relation);}
    mark(obs,Phase::Relation);
    let mut dot=crate::fast_pairing::EbyKDot::new();
    for (j,w) in a.weights.iter().enumerate() {dot.push(field(v.final_message,j),*w).map_err(|_|Error::Parse)?;}
    let actual=dot.finish();
    crate::trace::value(17,0,actual);crate::trace::value(17,1,a.rhs);
    if a.next!=22||actual!=a.rhs {return Err(Error::Query);}
    mark(obs,Phase::Final);Ok(())
}
}
