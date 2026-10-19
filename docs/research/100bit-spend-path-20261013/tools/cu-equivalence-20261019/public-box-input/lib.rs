// Source-preserving module layout for extraction-tool input review.
// Every declaration body is included unchanged from its recorded fragment.
// This layout is not compiled as part of kit generation.
extern crate alloc;

pub mod aspis_core {
pub trait Digest32: Copy {
    fn digest(&self, parts: &[&[u8]]) -> [u8; 32];
}
    pub mod field {
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

pub mod r1_wire {
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
    }
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

use alloc::vec::Vec;
use pool_v1::pair_forest_terminal::PoolV1PairForestTerminalStatementV1;
use pool_v1::pair_forest_semantic_terminal::r0::Public;
#[derive(Clone, Copy)]
struct SolanaDigest;
#[derive(Clone, Copy)]
struct DecodeError;
#[derive(Clone, Copy)]
enum ProgramError { InvalidAccountData, InvalidInstructionData }
fn decode_pool_v1_pair_forest_terminal_statement_v1(_: &[u8]) -> Result<PoolV1PairForestTerminalStatementV1, DecodeError> { unreachable!() }
mod verifier {
use super::*;
#[derive(Debug,Clone,Copy,PartialEq,Eq)]
pub enum Phase { Parsed,Semantic,SemanticPart(u8),Prepare,CheckpointRead,Merkle(usize),Query(usize),QueryPart(usize,u8),CheckpointWrite,Relation,Final }
pub type Observer = Option<fn(Phase)>;
#[derive(Clone, Copy)]
pub struct Error;
pub fn tx1(public: Public<'_>, public_bytes: &[u8], proof: &[u8], k: usize, hash: SolanaDigest, obs: Observer) -> Result<Vec<u8>, Error> { unreachable!() }
}
fn mark(_: verifier::Phase) { unreachable!() }
fn error(_: verifier::Error) -> ProgramError { unreachable!() }
#[inline(never)]
fn first(public_bytes:&[u8],proof:&[u8],k:usize)->Result<Vec<u8>,ProgramError>{
    let statement=decode_pool_v1_pair_forest_terminal_statement_v1(public_bytes).map_err(|_|ProgramError::InvalidAccountData)?;
    let public=statement.semantic_public();
    verifier::tx1(public,public_bytes,proof,k,SolanaDigest,Some(mark)).map_err(error)
}

use alloc::boxed::Box;
#[inline(never)]
fn decode_public_statement_box(
    bytes: &[u8],
) -> Result<Box<PoolV1PairForestTerminalStatementV1>, ProgramError> {
    Ok(Box::new(
        decode_pool_v1_pair_forest_terminal_statement_v1(bytes)
            .map_err(|_| ProgramError::InvalidAccountData)?,
    ))
}
