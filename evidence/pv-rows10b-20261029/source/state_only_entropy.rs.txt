//! Production host-side entropy and crash-safe mask-attempt reservation.
//!
//! Proof construction must reserve the public attempt nonce durably before
//! deriving either the affine field masks or the private Merkle salts.  The
//! reservation is append-only: a failed build or process crash burns it.

use std::fs::{self, File, OpenOptions};
use std::io::{self, Write};
use std::path::{Path, PathBuf};

#[cfg(unix)]
use std::os::unix::fs::OpenOptionsExt;

use aspis_core::state_only_hiding::{
    StateOnlyHidingContext, PINNED_POOL_V1_PAIR_FOREST_HIDING_LAYOUT_FACTOR_FINGERPRINT_V1,
    PINNED_POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_FINGERPRINT_V1,
    PINNED_POOL_V1_PAYMENT_RELATION_FREE_MASK_FINGERPRINT,
    PINNED_POOL_V1_PRIVATE_TRANSFER_HIDING_LAYOUT_FACTOR_FINGERPRINT,
    PINNED_POOL_V1_WITHDRAWAL_HIDING_LAYOUT_FACTOR_FINGERPRINT,
};
use aspis_core::state_only_masked_switch_basis::PINNED_MASKED_SWITCH_UNIVERSAL_CODE_BASIS_FINGERPRINT;
use aspis_core::HashFn;
use aspis_statement::{
    atomic_state_only_terminal::atomic_state_only_copy_active_rows_v3,
    pool_v1::{
        
        pool_v1_private_transfer_copy_active_row_masks_compiled_v1,
        pool_v1_withdrawal_copy_active_row_masks_compiled_v1,
    },
    STATE_ONLY_POSEIDON_TRACE_ROWS,
};
use sha2::{Digest, Sha256};
use zeroize::{Zeroize, Zeroizing};

use crate::state_only_hiding::{
    build_atomic_state_only_mask_material_v3_from_entropy_ref,
    build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref,
    build_pool_v1_private_transfer_mask_material_v1_from_entropy_ref,
    build_pool_v1_withdrawal_mask_material_v1_from_entropy_ref, StateOnlyMaskBuildError,
    StateOnlyMaskMaterial, StateOnlyMaskNonceStore,
};

#[cfg(not(feature="prover"))]
use aspis_statement::pool_v1::pool_v1_pair_forest_copy_active_row_masks_v1;
#[cfg(feature="prover")]
use crate::host_forest::pool_v1_pair_forest_copy_active_row_masks_v1 as pool_v1_pair_forest_copy_active_row_masks_v1;

const ATTEMPT_RESERVATION_DOMAIN: &[u8] = b"aspis:state-only:attempt-reservation:v1";
const PROFILE21_ATTEMPT_BINDING_DOMAIN: &[u8] = b"aspis:state-only:profile21:attempt-binding:v1";
const PROFILE22_PRIVATE_ATTEMPT_BINDING_DOMAIN: &[u8] =
    b"aspis:state-only:profile22-private:attempt-binding:v1";
const PROFILE22_PRIVATE_WIRE_DESCRIPTOR: &[u8] =
    b"profile=22;depths=17,17,15,13,11;widths=416,128,64,64,64;trees=c1,c2,w1,w2,w3";
// The domain-separator byte strings below are hashed into deterministic
// fixture entropy derivation; the committed unmined fixture (and its pinned
// regression values) must stay reproducible byte-for-byte against exactly
// these aspis-spend spellings.
const SPEND_PRIVATE_ATTEMPT_BINDING_DOMAIN: &[u8] =
    b"aspis:state-only:spend-zero-factor:attempt-binding:v1";
const SPEND_PRIVATE_WIRE_DESCRIPTOR: &[u8] =
    b"profile=spend;generators=H26,G27,D28;factorD=0;selector=3;depths=17,17,15,13,11;widths=416,192,64,64,64;trees=c1,c2,w1,w2,w3";
const SPEND_D_SEED_DOMAIN: &[u8] = b"aspis:state-only:spend:zero-factor-d-seed:v1";
const POOL_V1_PRIVATE_ATTEMPT_BINDING_DOMAIN: &[u8] =
    b"aspis:state-only:pool-v1:private-attempt-binding:v1";
const POOL_V1_PRIVATE_WIRE_DESCRIPTOR: &[u8] =
    b"profile=pool-v1-tag73;generators=H26,G27,D28;factorD=0;rows=1024;c1=16;selected=28;theta=29;queries=16;first-cap=203";
const POOL_V1_SOURCE_SEED_DOMAIN: &[u8] = b"aspis:state-only:pool-v1:source-seed:v1";
const POOL_V1_D_SEED_DOMAIN: &[u8] = b"aspis:state-only:pool-v1:zero-factor-d-seed:v1";
const PROFILE21_SOURCE_SEED_DOMAIN: &[u8] = b"aspis:state-only:profile21:source-seed:v1";
const PROFILE21_SOURCE_EXPAND_DOMAIN: &[u8] = b"aspis:state-only:profile21:source-expand:v1";
const LEAF_SALT_DOMAIN: &[u8] = b"aspis:state-only:private-leaf-salt:v1";
const RESERVATION_MAGIC: &[u8; 16] = b"ASPIS-MASK-V1\0\0\0";
const ENTROPY_RETRY_LIMIT: usize = 16;

#[derive(Debug)]
pub enum StateOnlyAttemptEntropyError {
    Os(getrandom::Error),
    RepeatedZeroBlock,
}

impl From<getrandom::Error> for StateOnlyAttemptEntropyError {
    fn from(value: getrandom::Error) -> Self {
        Self::Os(value)
    }
}

/// Three independent 256-bit attempt values sampled from the operating
/// system. The public nonce is serialized; both private seeds are zeroized on
/// drop. The field seed and leaf-salt seed are never derived from one another.
pub struct StateOnlyAttemptSecrets {
    mask_nonce: [u8; 32],
    field_mask_entropy: Zeroizing<[u8; 32]>,
    leaf_salt_seed: Zeroizing<[u8; 32]>,
}

/// A successful durable reservation and affine-mask build is the only way to
/// obtain this type. Private leaf salts therefore cannot be derived before
/// the public attempt nonce is burned.
pub struct ReservedStateOnlyAttemptSecrets {
    mask_nonce: [u8; 32],
    precommit_binding: [u8; 32],
    reserved_context: StateOnlyHidingContext,
    leaf_salt_seed: Zeroizing<[u8; 32]>,
    source_mask_seed: Zeroizing<[u8; 32]>,
}

struct SensitiveQm31Vec(Vec<aspis_core::field::QM31>);

impl Drop for SensitiveQm31Vec {
    fn drop(&mut self) {
        let zero=aspis_core::field::QM31::ZERO;
        let count=self.0.len();let mut index=0;
        while index<count {
            crate::state_only_hiding::volatile_clear_cell(&mut self.0[index],zero);
            index+=1;
        }
        core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
    }
}

#[inline(always)]
fn entropy_nonzero32(bytes:&[u8;32])->bool {
    let mut combined=0u8;let mut i=0;
    while i<32 {combined|=bytes[i];i+=1;}
    combined!=0
}

impl StateOnlyAttemptSecrets {
    /// Construct fixed attempt secrets for a byte-exact profile-21 fixture.
    ///
    /// This API does not exist in a default or production build. Enabling the
    /// feature that exposes it is unsafe for proof generation because reusing
    /// these values reuses both affine-mask entropy and private-leaf salts.
    #[cfg(any(test, feature = "insecure-profile21-fixture"))]
    pub fn deterministic_profile21_fixture(
        mask_nonce: [u8; 32],
        field_mask_entropy: [u8; 32],
        leaf_salt_seed: [u8; 32],
    ) -> Self {
        assert_ne!(mask_nonce, [0; 32]);
        assert_ne!(field_mask_entropy, [0; 32]);
        assert_ne!(leaf_salt_seed, [0; 32]);
        Self {
            mask_nonce,
            field_mask_entropy: Zeroizing::new(field_mask_entropy),
            leaf_salt_seed: Zeroizing::new(leaf_salt_seed),
        }
    }

    /// Construct fixed attempt secrets for the byte-exact profile-22 fixture.
    /// This is deliberately absent from production builds.
    #[cfg(any(test, feature = "insecure-profile22-fixture"))]
    pub fn deterministic_profile22_fixture(
        mask_nonce: [u8; 32],
        field_mask_entropy: [u8; 32],
        leaf_salt_seed: [u8; 32],
    ) -> Self {
        assert_ne!(mask_nonce, [0; 32]);
        assert_ne!(field_mask_entropy, [0; 32]);
        assert_ne!(leaf_salt_seed, [0; 32]);
        Self {
            mask_nonce,
            field_mask_entropy: Zeroizing::new(field_mask_entropy),
            leaf_salt_seed: Zeroizing::new(leaf_salt_seed),
        }
    }

    /// Construct fixed attempt secrets for a byte-exact, nondefault
    /// spend fixture. This API is never present in a production build.
    #[cfg(any(test, feature = "insecure-spend-fixture"))]
    pub fn deterministic_spend_fixture(
        mask_nonce: [u8; 32],
        field_mask_entropy: [u8; 32],
        leaf_salt_seed: [u8; 32],
    ) -> Self {
        assert_ne!(mask_nonce, [0; 32]);
        assert_ne!(field_mask_entropy, [0; 32]);
        assert_ne!(leaf_salt_seed, [0; 32]);
        Self {
            mask_nonce,
            field_mask_entropy: Zeroizing::new(field_mask_entropy),
            leaf_salt_seed: Zeroizing::new(leaf_salt_seed),
        }
    }

    pub fn generate() -> Result<Self, StateOnlyAttemptEntropyError> {
        for _ in 0..ENTROPY_RETRY_LIMIT {
            let mut bytes = Zeroizing::new([0u8; 96]);
            getrandom::fill(bytes.as_mut())?;

            let mut mask_nonce = [0u8; 32];
            let mut field_mask_entropy = Zeroizing::new([0u8; 32]);
            let mut leaf_salt_seed = Zeroizing::new([0u8; 32]);
            mask_nonce.copy_from_slice(&bytes[..32]);
            field_mask_entropy.copy_from_slice(&bytes[32..64]);
            leaf_salt_seed.copy_from_slice(&bytes[64..]);

            if mask_nonce != [0; 32] && *field_mask_entropy != [0; 32] && *leaf_salt_seed != [0; 32]
            {
                return Ok(Self {
                    mask_nonce,
                    field_mask_entropy,
                    leaf_salt_seed,
                });
            }
        }
        Err(StateOnlyAttemptEntropyError::RepeatedZeroBlock)
    }

    /// Generate fresh private attempt entropy for a preselected public nonce.
    ///
    /// A deployed proof binds this nonce to the proof-account address. Clients
    /// therefore generate the account keypair first and pass its public key
    /// here. The public nonce only needs to be unique; both secret seeds still
    /// come independently from the operating system and are zeroized on drop.
    pub fn generate_for_mask_nonce(
        mask_nonce: [u8; 32],
    ) -> Result<Self, StateOnlyAttemptEntropyError> {
        let limit=ENTROPY_RETRY_LIMIT;

        if !entropy_nonzero32(&mask_nonce) {
            return Err(StateOnlyAttemptEntropyError::RepeatedZeroBlock);
        }
        let mut retry=0;
        while retry<limit {
            let mut bytes = Zeroizing::new([0u8; 64]);
            getrandom::fill(bytes.as_mut())?;

            let mut field_mask_entropy = Zeroizing::new([0u8; 32]);
            let mut leaf_salt_seed = Zeroizing::new([0u8; 32]);
            field_mask_entropy.copy_from_slice(&bytes[..32]);
            leaf_salt_seed.copy_from_slice(&bytes[32..]);
            if entropy_nonzero32(&field_mask_entropy) && entropy_nonzero32(&leaf_salt_seed) {
                return Ok(Self {
                    mask_nonce,
                    field_mask_entropy,
                    leaf_salt_seed,
                });
            }
            retry+=1;
        }
        Err(StateOnlyAttemptEntropyError::RepeatedZeroBlock)
    }

    pub fn mask_nonce(&self) -> [u8; 32] {
        self.mask_nonce
    }

    /// Durably burn the public nonce, then build the atomic affine masks.
    /// Success returns the only type capable of deriving private leaf salts.
    /// Any later build failure drops and zeroizes both private seeds while the
    /// durable reservation remains present.
    pub fn reserve_and_build_atomic_mask_material_v3(
        mut self,
        hash: HashFn,
        precommit_binding: [u8; 32],
        context: StateOnlyHidingContext,
        nonce_store: &mut impl StateOnlyMaskNonceStore,
    ) -> Result<(ReservedStateOnlyAttemptSecrets, StateOnlyMaskMaterial), StateOnlyMaskBuildError>
    {
        if context.mask_nonce != self.mask_nonce {
            return Err(StateOnlyMaskBuildError::Layout);
        }
        if !nonce_store.reserve(context.statement_digest, context.mask_nonce) {
            return Err(StateOnlyMaskBuildError::ReusedMaskNonce);
        }
        // The ordinary builder retains its exact reserve-before-derivation
        // invariant. This single-use adapter acknowledges the reservation
        // already made durably above without touching storage a second time.
        let mut pre_reserved = PreReservedNonce {
            statement_digest: context.statement_digest,
            mask_nonce: context.mask_nonce,
            consumed: false,
        };
        let material = build_atomic_state_only_mask_material_v3_from_entropy_ref(
            hash,
            precommit_binding,
            context,
            &self.field_mask_entropy,
            &mut pre_reserved,
        )?;
        if !pre_reserved.consumed {
            return Err(StateOnlyMaskBuildError::ReusedMaskNonce);
        }
        let source_mask_seed = Zeroizing::new(hash(&[
            PROFILE21_SOURCE_SEED_DOMAIN,
            &precommit_binding,
            &context.encode(),
            self.field_mask_entropy.as_ref(),
        ]));
        self.field_mask_entropy.zeroize();
        Ok((
            ReservedStateOnlyAttemptSecrets {
                mask_nonce: self.mask_nonce,
                precommit_binding,
                reserved_context: context,
                leaf_salt_seed: self.leaf_salt_seed,
                source_mask_seed,
            },
            material,
        ))
    }

    pub fn reserve_and_build_pool_v1_private_transfer_mask_material_v1(
        mut self,
        hash: HashFn,
        precommit_binding: [u8; 32],
        context: StateOnlyHidingContext,
        nonce_store: &mut impl StateOnlyMaskNonceStore,
    ) -> Result<(ReservedStateOnlyAttemptSecrets, StateOnlyMaskMaterial), StateOnlyMaskBuildError>
    {
        if context.mask_nonce != self.mask_nonce
            || context.mask_layout_fingerprint
                != PINNED_POOL_V1_PAYMENT_RELATION_FREE_MASK_FINGERPRINT
            || context.layout_factor_fingerprint
                != PINNED_POOL_V1_PRIVATE_TRANSFER_HIDING_LAYOUT_FACTOR_FINGERPRINT
        {
            return Err(StateOnlyMaskBuildError::Layout);
        }
        if !nonce_store.reserve(context.statement_digest, context.mask_nonce) {
            return Err(StateOnlyMaskBuildError::ReusedMaskNonce);
        }
        let mut pre_reserved = PreReservedNonce {
            statement_digest: context.statement_digest,
            mask_nonce: context.mask_nonce,
            consumed: false,
        };
        let material = build_pool_v1_private_transfer_mask_material_v1_from_entropy_ref(
            hash,
            precommit_binding,
            context,
            &self.field_mask_entropy,
            &mut pre_reserved,
        )?;
        if !pre_reserved.consumed {
            return Err(StateOnlyMaskBuildError::ReusedMaskNonce);
        }
        let source_mask_seed = Zeroizing::new(hash(&[
            POOL_V1_SOURCE_SEED_DOMAIN,
            &precommit_binding,
            &context.encode(),
            self.field_mask_entropy.as_ref(),
        ]));
        self.field_mask_entropy.zeroize();
        Ok((
            ReservedStateOnlyAttemptSecrets {
                mask_nonce: self.mask_nonce,
                precommit_binding,
                reserved_context: context,
                leaf_salt_seed: self.leaf_salt_seed,
                source_mask_seed,
            },
            material,
        ))
    }

    pub fn reserve_and_build_pool_v1_withdrawal_mask_material_v1(
        mut self,
        hash: HashFn,
        precommit_binding: [u8; 32],
        context: StateOnlyHidingContext,
        nonce_store: &mut impl StateOnlyMaskNonceStore,
    ) -> Result<(ReservedStateOnlyAttemptSecrets, StateOnlyMaskMaterial), StateOnlyMaskBuildError>
    {
        if context.mask_nonce != self.mask_nonce
            || context.mask_layout_fingerprint
                != PINNED_POOL_V1_PAYMENT_RELATION_FREE_MASK_FINGERPRINT
            || context.layout_factor_fingerprint
                != PINNED_POOL_V1_WITHDRAWAL_HIDING_LAYOUT_FACTOR_FINGERPRINT
        {
            return Err(StateOnlyMaskBuildError::Layout);
        }
        if !nonce_store.reserve(context.statement_digest, context.mask_nonce) {
            return Err(StateOnlyMaskBuildError::ReusedMaskNonce);
        }
        let mut pre_reserved = PreReservedNonce {
            statement_digest: context.statement_digest,
            mask_nonce: context.mask_nonce,
            consumed: false,
        };
        let material = build_pool_v1_withdrawal_mask_material_v1_from_entropy_ref(
            hash,
            precommit_binding,
            context,
            &self.field_mask_entropy,
            &mut pre_reserved,
        )?;
        if !pre_reserved.consumed {
            return Err(StateOnlyMaskBuildError::ReusedMaskNonce);
        }
        let source_mask_seed = Zeroizing::new(hash(&[
            POOL_V1_SOURCE_SEED_DOMAIN,
            &precommit_binding,
            &context.encode(),
            self.field_mask_entropy.as_ref(),
        ]));
        self.field_mask_entropy.zeroize();
        Ok((
            ReservedStateOnlyAttemptSecrets {
                mask_nonce: self.mask_nonce,
                precommit_binding,
                reserved_context: context,
                leaf_salt_seed: self.leaf_salt_seed,
                source_mask_seed,
            },
            material,
        ))
    }

    pub fn reserve_and_build_pool_v1_pair_forest_mask_material_v1(
        mut self,
        hash: HashFn,
        precommit_binding: [u8; 32],
        context: StateOnlyHidingContext,
        nonce_store: &mut impl StateOnlyMaskNonceStore,
    ) -> Result<(ReservedStateOnlyAttemptSecrets, StateOnlyMaskMaterial), StateOnlyMaskBuildError>
    {
        if context.mask_nonce != self.mask_nonce
            || context.mask_layout_fingerprint
                != PINNED_POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_FINGERPRINT_V1
            || context.layout_factor_fingerprint
                != PINNED_POOL_V1_PAIR_FOREST_HIDING_LAYOUT_FACTOR_FINGERPRINT_V1
        {
            return Err(StateOnlyMaskBuildError::Layout);
        }
        if !nonce_store.reserve(context.statement_digest, context.mask_nonce) {
            return Err(StateOnlyMaskBuildError::ReusedMaskNonce);
        }
        let mut pre_reserved = PreReservedNonce {
            statement_digest: context.statement_digest,
            mask_nonce: context.mask_nonce,
            consumed: false,
        };
        let material = build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref(
            hash,
            precommit_binding,
            context,
            &self.field_mask_entropy,
            &mut pre_reserved,
        )?;
        if !pre_reserved.consumed {
            return Err(StateOnlyMaskBuildError::ReusedMaskNonce);
        }
        let source_mask_seed = Zeroizing::new(hash(&[
            POOL_V1_SOURCE_SEED_DOMAIN,
            &precommit_binding,
            &context.encode(),
            self.field_mask_entropy.as_ref(),
        ]));
        self.field_mask_entropy.zeroize();
        Ok((
            ReservedStateOnlyAttemptSecrets {
                mask_nonce: self.mask_nonce,
                precommit_binding,
                reserved_context: context,
                leaf_salt_seed: self.leaf_salt_seed,
                source_mask_seed,
            },
            material,
        ))
    }
}

struct PreReservedNonce {
    statement_digest: [u8; 32],
    mask_nonce: [u8; 32],
    consumed: bool,
}

impl StateOnlyMaskNonceStore for PreReservedNonce {
    fn reserve(&mut self, statement_digest: [u8; 32], mask_nonce: [u8; 32]) -> bool {
        if self.consumed
            || statement_digest != self.statement_digest
            || mask_nonce != self.mask_nonce
        {
            return false;
        }
        self.consumed = true;
        true
    }
}

impl ReservedStateOnlyAttemptSecrets {
    pub fn mask_nonce(&self) -> [u8; 32] {
        self.mask_nonce
    }

    /// Derive one profile-21 private salt from the canonical attempt binding.
    /// Callers cannot omit the statement, mask/layout, source-basis or burned
    /// nonce fields from this binding.
    pub fn derive_profile21_leaf_salt(
        &self,
        hash: HashFn,
        context: StateOnlyHidingContext,
        tree_tag: u8,
        leaf_index: u32,
    ) -> Result<[u8; 32], StateOnlyMaskBuildError> {
        if context.mask_nonce != self.mask_nonce {
            return Err(StateOnlyMaskBuildError::Layout);
        }
        let attempt_binding = profile21_attempt_binding(hash, &self.precommit_binding, context);
        Ok(hash(&[
            LEAF_SALT_DOMAIN,
            &attempt_binding,
            &self.mask_nonce,
            &[tree_tag],
            &leaf_index.to_le_bytes(),
            self.leaf_salt_seed.as_ref(),
        ]))
    }

    /// Derive one profile-22 private salt without importing profile 21's
    /// retired masked-switch basis into the attempt binding.
    pub fn derive_profile22_leaf_salt(
        &self,
        hash: HashFn,
        context: StateOnlyHidingContext,
        tree_tag: u8,
        leaf_index: u32,
    ) -> Result<[u8; 32], StateOnlyMaskBuildError> {
        if context.mask_nonce != self.mask_nonce {
            return Err(StateOnlyMaskBuildError::Layout);
        }
        let attempt_binding =
            profile22_private_attempt_binding(hash, &self.precommit_binding, context);
        Ok(hash(&[
            LEAF_SALT_DOMAIN,
            &attempt_binding,
            &self.mask_nonce,
            &[tree_tag],
            &leaf_index.to_le_bytes(),
            self.leaf_salt_seed.as_ref(),
        ]))
    }

    /// Spend salt binding includes the widened C2 descriptor and the
    /// q3 selector envelope, so no private opening can be replayed as p22.
    pub fn derive_spend_leaf_salt(
        &self,
        hash: HashFn,
        context: StateOnlyHidingContext,
        tree_tag: u8,
        leaf_index: u32,
    ) -> Result<[u8; 32], StateOnlyMaskBuildError> {
        if context.mask_nonce != self.mask_nonce {
            return Err(StateOnlyMaskBuildError::Layout);
        }
        let attempt_binding = spend_private_attempt_binding(hash, &self.precommit_binding, context);
        Ok(hash(&[
            LEAF_SALT_DOMAIN,
            &attempt_binding,
            &self.mask_nonce,
            &[tree_tag],
            &leaf_index.to_le_bytes(),
            self.leaf_salt_seed.as_ref(),
        ]))
    }

    fn validate_pool_v1_context(
        &self,
        context: StateOnlyHidingContext,
    ) -> Result<(), StateOnlyMaskBuildError> {
        let legacy = context.mask_layout_fingerprint
            == PINNED_POOL_V1_PAYMENT_RELATION_FREE_MASK_FINGERPRINT
            && matches!(
                context.layout_factor_fingerprint,
                PINNED_POOL_V1_PRIVATE_TRANSFER_HIDING_LAYOUT_FACTOR_FINGERPRINT
                    | PINNED_POOL_V1_WITHDRAWAL_HIDING_LAYOUT_FACTOR_FINGERPRINT
            );
        let forest = context.mask_layout_fingerprint
            == PINNED_POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_FINGERPRINT_V1
            && context.layout_factor_fingerprint
                == PINNED_POOL_V1_PAIR_FOREST_HIDING_LAYOUT_FACTOR_FINGERPRINT_V1;
        if context != self.reserved_context
            || context.mask_nonce != self.mask_nonce
            || !(legacy || forest)
        {
            return Err(StateOnlyMaskBuildError::Layout);
        }
        Ok(())
    }

    /// Derive one Pool V1 private tree salt under the complete width-29
    /// Tag-73 attempt descriptor. The exact reserved statement and variant
    /// context must be replayed; atomic/spend and crossed Pool contexts fail.
    pub fn derive_pool_v1_leaf_salt(
        &self,
        hash: HashFn,
        context: StateOnlyHidingContext,
        tree_tag: u8,
        leaf_index: u32,
    ) -> Result<[u8; 32], StateOnlyMaskBuildError> {
        self.validate_pool_v1_context(context)?;
        let attempt_binding =
            pool_v1_private_attempt_binding(hash, &self.precommit_binding, context);
        Ok(hash(&[
            LEAF_SALT_DOMAIN,
            &attempt_binding,
            &self.mask_nonce,
            &[tree_tag],
            &leaf_index.to_le_bytes(),
            self.leaf_salt_seed.as_ref(),
        ]))
    }

    /// Expand one independently domain-separated full-domain QM31 D lane.
    /// Values on copy-inactive rows have zero sum, matching the raw-block
    /// balancing convention used by G/H1 while leaving every active row and
    /// all four tower coordinates private. D is not passed to the H oracle.
    pub fn derive_spend_zero_factor_d(
        &self,
        hash: HashFn,
        context: StateOnlyHidingContext,
    ) -> Result<Vec<aspis_core::field::QM31>, StateOnlyMaskBuildError> {
        if context.mask_nonce != self.mask_nonce
            || context.layout_factor_fingerprint
                != aspis_core::state_only_hiding::PINNED_ATOMIC_STATE_ONLY_SPEND_LAYOUT_FACTOR_FINGERPRINT_V3
        {
            return Err(StateOnlyMaskBuildError::Layout);
        }
        let attempt_binding = spend_private_attempt_binding(hash, &self.precommit_binding, context);
        let mut expander = Profile21SourceExpander::new(
            hash,
            hash(&[
                SPEND_D_SEED_DOMAIN,
                &attempt_binding,
                self.source_mask_seed.as_ref(),
            ]),
        );
        let mut d = SensitiveQm31Vec(Vec::with_capacity(STATE_ONLY_POSEIDON_TRACE_ROWS));
        for _ in 0..STATE_ONLY_POSEIDON_TRACE_ROWS {
            d.0.push(expander.qm31()?);
        }
        let mut active = [false; STATE_ONLY_POSEIDON_TRACE_ROWS];
        for &row in atomic_state_only_copy_active_rows_v3() {
            active[usize::from(row)] = true;
        }
        let dependent = active
            .iter()
            .position(|is_active| !*is_active)
            .ok_or(StateOnlyMaskBuildError::Layout)?;
        let sum =
            d.0.iter()
                .copied()
                .enumerate()
                .filter(|(row, _)| !active[*row] && *row != dependent)
                .fold(aspis_core::field::QM31::ZERO, |sum, value| sum.add(value.1));
        d.0[dependent] = aspis_core::field::QM31::ZERO.sub(sum);
        Ok(core::mem::take(&mut d.0))
    }

    fn derive_pool_v1_zero_factor_d(
        &self,
        hash: HashFn,
        context: StateOnlyHidingContext,
        expected_factor_fingerprint: u64,
        active_masks: &[u16; 64],
    ) -> Result<Vec<aspis_core::field::QM31>, StateOnlyMaskBuildError> {
        self.validate_pool_v1_context(context)?;
        if context.layout_factor_fingerprint != expected_factor_fingerprint {
            return Err(StateOnlyMaskBuildError::Layout);
        }
        let attempt_binding =
            pool_v1_private_attempt_binding(hash, &self.precommit_binding, context);
        let mut expander = Profile21SourceExpander::new(
            hash,
            hash(&[
                POOL_V1_D_SEED_DOMAIN,
                &attempt_binding,
                self.source_mask_seed.as_ref(),
            ]),
        );
        let mut d=sample_source_d(&mut expander)?;
        let active=source_active_flags(active_masks);
        balance_source_d(&mut d.0,&active)?;
        Ok(core::mem::take(&mut d.0))
    }

    pub fn derive_pool_v1_private_transfer_zero_factor_d(
        &self,
        hash: HashFn,
        context: StateOnlyHidingContext,
    ) -> Result<Vec<aspis_core::field::QM31>, StateOnlyMaskBuildError> {
        self.derive_pool_v1_zero_factor_d(
            hash,
            context,
            PINNED_POOL_V1_PRIVATE_TRANSFER_HIDING_LAYOUT_FACTOR_FINGERPRINT,
            pool_v1_private_transfer_copy_active_row_masks_compiled_v1(),
        )
    }

    pub fn derive_pool_v1_withdrawal_zero_factor_d(
        &self,
        hash: HashFn,
        context: StateOnlyHidingContext,
    ) -> Result<Vec<aspis_core::field::QM31>, StateOnlyMaskBuildError> {
        self.derive_pool_v1_zero_factor_d(
            hash,
            context,
            PINNED_POOL_V1_WITHDRAWAL_HIDING_LAYOUT_FACTOR_FINGERPRINT,
            pool_v1_withdrawal_copy_active_row_masks_compiled_v1(),
        )
    }

    pub fn derive_pool_v1_pair_forest_zero_factor_d(
        &self,
        hash: HashFn,
        context: StateOnlyHidingContext,
    ) -> Result<Vec<aspis_core::field::QM31>, StateOnlyMaskBuildError> {
        let active_masks = pool_v1_pair_forest_copy_active_row_masks_v1()
            .map_err(|_| StateOnlyMaskBuildError::Layout)?;
        self.derive_pool_v1_zero_factor_d(
            hash,
            context,
            PINNED_POOL_V1_PAIR_FOREST_HIDING_LAYOUT_FACTOR_FINGERPRINT_V1,
            &active_masks,
        )
    }

    /// Deterministically expand the reserved attempt's field-mask domain into
    /// the two independent 35-QM31 logical source words `(X,F)`. This method
    /// exists only on the post-reservation typestate, so neither source word
    /// can be generated under an unburned public attempt nonce.
    pub fn derive_profile21_source_masks(
        &self,
        hash: HashFn,
        context: StateOnlyHidingContext,
    ) -> Result<
        ([aspis_core::field::QM31; 35], [aspis_core::field::QM31; 35]),
        StateOnlyMaskBuildError,
    > {
        if context.mask_nonce != self.mask_nonce {
            return Err(StateOnlyMaskBuildError::Layout);
        }
        let attempt_binding = profile21_attempt_binding(hash, &self.precommit_binding, context);
        let mut expander = Profile21SourceExpander::new(
            hash,
            hash(&[
                PROFILE21_SOURCE_SEED_DOMAIN,
                &attempt_binding,
                self.source_mask_seed.as_ref(),
            ]),
        );
        let mut x = [aspis_core::field::QM31::ZERO; 35];
        let mut f = [aspis_core::field::QM31::ZERO; 35];
        for value in x.iter_mut().chain(f.iter_mut()) {
            *value = expander.qm31()?;
        }
        Ok((x, f))
    }
}

fn sample_source_d(expander:&mut Profile21SourceExpander)->Result<SensitiveQm31Vec,StateOnlyMaskBuildError> {
    let rows=STATE_ONLY_POSEIDON_TRACE_ROWS;
    let mut d=SensitiveQm31Vec(Vec::with_capacity(rows));
    let mut row=0;
    while row<rows {
        let value=expander.qm31()?;
        d.0.push(value);row+=1;
    }
    Ok(d)
}
fn source_active_flags(masks:&[u16;64])->[bool;STATE_ONLY_POSEIDON_TRACE_ROWS] {
    let rows=STATE_ONLY_POSEIDON_TRACE_ROWS;

    let mut active=[false;STATE_ONLY_POSEIDON_TRACE_ROWS];let mut row=0;
    while row<rows {
        active[row]=masks[row>>4]&(1<<(row&15))!=0;row+=1;
    }
    active
}
fn balance_source_d(d:&mut[aspis_core::field::QM31],active:&[bool;STATE_ONLY_POSEIDON_TRACE_ROWS])->Result<(),StateOnlyMaskBuildError> {
    let dependent=source_dependent_row(active)?;
    let sum=source_inactive_sum(d,active,dependent);
    let value=aspis_core::field::QM31::ZERO.sub(sum);
    d[dependent]=value;
    Ok(())
}
fn source_dependent_row(active:&[bool;STATE_ONLY_POSEIDON_TRACE_ROWS])->Result<usize,StateOnlyMaskBuildError> {
    let rows=STATE_ONLY_POSEIDON_TRACE_ROWS;let mut dependent=0;
    while dependent<rows && active[dependent] {dependent+=1;}
    if dependent==rows {return Err(StateOnlyMaskBuildError::Layout);}
    Ok(dependent)
}
fn source_inactive_sum(d:&[aspis_core::field::QM31],active:&[bool;STATE_ONLY_POSEIDON_TRACE_ROWS],dependent:usize)->aspis_core::field::QM31 {
    let rows=STATE_ONLY_POSEIDON_TRACE_ROWS;
    let mut sum=aspis_core::field::QM31::ZERO;let mut row=0;
    while row<rows {
        sum=source_inactive_step(sum,d,active,dependent,row);
        row+=1;
    }
    sum
}

#[inline(always)]
fn source_inactive_step(sum:aspis_core::field::QM31,d:&[aspis_core::field::QM31],active:&[bool;STATE_ONLY_POSEIDON_TRACE_ROWS],dependent:usize,row:usize)->aspis_core::field::QM31 {
    if !active[row] && row!=dependent {sum.add(d[row])} else {sum}
}

struct Profile21SourceExpander {
    hash: HashFn,
    seed: Zeroizing<[u8; 32]>,
    counter: u64,
    block: [u8; 32],
    word: usize,
}

impl Profile21SourceExpander {
    fn new(hash: HashFn, seed: [u8; 32]) -> Self {
        Self {
            hash,
            seed: Zeroizing::new(seed),
            counter: 0,
            block: [0; 32],
            word: 8,
        }
    }

    #[cfg_attr(kani, kani::requires(self.word <= 8))]
    #[cfg_attr(kani, kani::requires(self.hash == crate::HOST_HASH))]
    #[cfg_attr(kani, kani::requires(crate::prover_commit_oracle::expander_domain(
        b"aspis:state-only:profile21:source-expand:v1", *self.seed, self.counter, self.word)))]
    #[cfg_attr(kani, kani::modifies(&mut self.counter, &mut self.block, &mut self.word))]
    #[cfg_attr(kani, kani::ensures(|result| crate::prover_commit_reference::next_matches(
        b"aspis:state-only:profile21:source-expand:v1",
        crate::prover_commit_reference::State { seed: old(*self.seed), counter: old(self.counter), block: old(self.block), word: old(self.word) },
        *result,
        crate::prover_commit_reference::State { seed: *self.seed, counter: self.counter, block: self.block, word: self.word })))]
    fn next_word(&mut self) -> u32 {
        if self.word == 8 {
            let hash = self.hash;
            let seed: [u8; 32] = *self.seed;
            let counter = self.counter;
            self.block = profile21_source_expander_block(hash, seed, counter);
            self.counter = self.counter.wrapping_add(1);
            self.word = 0;
        }
        let start = 4 * self.word;
        self.word += 1;
        u32::from_le_bytes(self.block[start..start + 4].try_into().unwrap())
    }

    fn m31(&mut self) -> Result<aspis_core::field::M31, StateOnlyMaskBuildError> {
        let mut retry=0;
        while retry<16 {
            let candidate=self.next_word() & 0x7fff_ffff;
            if candidate<aspis_core::field::P {return Ok(aspis_core::field::M31(candidate));}
            retry+=1;
        }
        Err(StateOnlyMaskBuildError::MaskSampleExhausted)
    }

    fn qm31(&mut self) -> Result<aspis_core::field::QM31, StateOnlyMaskBuildError> {
        Ok(aspis_core::field::QM31 {
            c0: aspis_core::field::CM31::new(self.m31()?, self.m31()?),
            c1: aspis_core::field::CM31::new(self.m31()?, self.m31()?),
        })
    }
}

impl Drop for Profile21SourceExpander {
    fn drop(&mut self) {
        self.block.zeroize();
        self.counter.zeroize();
        self.word.zeroize();
    }
}

/// Canonical public binding shared by every field-mask and private-leaf
/// derivation in one profile-21 attempt.
pub fn profile21_attempt_binding(
    hash: HashFn,
    precommit_binding: &[u8; 32],
    context: StateOnlyHidingContext,
) -> [u8; 32] {
    hash(&[
        PROFILE21_ATTEMPT_BINDING_DOMAIN,
        precommit_binding,
        &context.encode(),
        &PINNED_MASKED_SWITCH_UNIVERSAL_CODE_BASIS_FINGERPRINT.to_le_bytes(),
    ])
}

/// Canonical profile-22 salt binding.  It deliberately has no source-code or
/// switch-basis input because profile 22 is the ordinary width-28 protocol.
pub fn profile22_private_attempt_binding(
    hash: HashFn,
    precommit_binding: &[u8; 32],
    context: StateOnlyHidingContext,
) -> [u8; 32] {
    hash(&[
        PROFILE22_PRIVATE_ATTEMPT_BINDING_DOMAIN,
        precommit_binding,
        &context.encode(),
        PROFILE22_PRIVATE_WIRE_DESCRIPTOR,
    ])
}

pub fn spend_private_attempt_binding(
    hash: HashFn,
    precommit_binding: &[u8; 32],
    context: StateOnlyHidingContext,
) -> [u8; 32] {
    hash(&[
        SPEND_PRIVATE_ATTEMPT_BINDING_DOMAIN,
        precommit_binding,
        &context.encode(),
        SPEND_PRIVATE_WIRE_DESCRIPTOR,
    ])
}

pub fn pool_v1_private_attempt_binding(
    hash: HashFn,
    precommit_binding: &[u8; 32],
    context: StateOnlyHidingContext,
) -> [u8; 32] {
    hash(&[
        POOL_V1_PRIVATE_ATTEMPT_BINDING_DOMAIN,
        precommit_binding,
        &context.encode(),
        POOL_V1_PRIVATE_WIRE_DESCRIPTOR,
    ])
}

/// Append-only filesystem-backed nonce ledger. `create_new` is the
/// concurrency linearization point; file and directory `fsync` make a
/// successful reservation durable before mask derivation. Any I/O error is
/// fail-closed through the boolean trait and is retained for diagnostics.
pub struct DurableStateOnlyMaskNonceStore {
    directory: PathBuf,
    last_error: Option<io::ErrorKind>,
}

impl DurableStateOnlyMaskNonceStore {
    pub fn open(directory: impl AsRef<Path>) -> io::Result<Self> {
        fs::create_dir_all(directory.as_ref())?;
        let metadata = fs::metadata(directory.as_ref())?;
        if !metadata.is_dir() {
            return Err(io::Error::new(
                io::ErrorKind::NotADirectory,
                "mask nonce ledger path is not a directory",
            ));
        }
        Ok(Self {
            directory: directory.as_ref().to_path_buf(),
            last_error: None,
        })
    }

    pub fn last_error(&self) -> Option<io::ErrorKind> {
        self.last_error
    }

    fn reservation_path(&self, mask_nonce: &[u8; 32]) -> PathBuf {
        // The nonce is burned globally within this wallet ledger, even if a
        // caller tries to reuse it under a different statement digest.
        let mut hasher = Sha256::new();
        hasher.update(ATTEMPT_RESERVATION_DOMAIN);
        hasher.update(mask_nonce);
        let digest: [u8; 32] = hasher.finalize().into();
        let name = reservation_name(digest,String::with_capacity(69),0);
        self.directory.join(name)
    }

    pub fn reserve_fallible(
        &mut self,
        statement_digest: [u8; 32],
        mask_nonce: [u8; 32],
    ) -> io::Result<bool> {
        self.last_error = None;
        let path = self.reservation_path(&mask_nonce);
        let mut options = OpenOptions::new();
        options.write(true).create_new(true);
        #[cfg(unix)]
        options.mode(0o600);
        let mut file = match options.open(path) {
            Ok(file) => file,
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => return Ok(false),
            Err(error) => return Err(error),
        };

        // A partially written file is still a burned nonce. Never remove it
        // on failure.
        file.write_all(RESERVATION_MAGIC)?;
        file.write_all(&statement_digest)?;
        file.write_all(&mask_nonce)?;
        file.sync_all()?;
        sync_directory(&self.directory)?;
        Ok(true)
    }
}

fn reservation_name(digest:[u8;32],mut name:String,i:usize)->String {
    if i==32 {
        name.push_str(".burn");
        return name;
    }
    let digits=["0","1","2","3","4","5","6","7","8","9","a","b","c","d","e","f"];
    let byte=digest[i];
    let high=digits[(byte>>4) as usize];
    let low=digits[(byte&15) as usize];
    name.push_str(high);
    name.push_str(low);
    reservation_name(digest,name,i+1)
}

impl StateOnlyMaskNonceStore for DurableStateOnlyMaskNonceStore {
    fn reserve(&mut self, statement_digest: [u8; 32], mask_nonce: [u8; 32]) -> bool {
        match self.reserve_fallible(statement_digest, mask_nonce) {
            Ok(reserved) => reserved,
            Err(error) => {
                self.last_error = Some(error.kind());
                false
            }
        }
    }
}

#[cfg(unix)]
fn sync_directory(directory: &Path) -> io::Result<()> {
    File::open(directory)?.sync_all()
}

#[cfg(not(unix))]
fn sync_directory(_directory: &Path) -> io::Result<()> {
    // `create_new` remains atomic. Platforms without directory-fsync support
    // must place this ledger on a storage layer whose metadata is durable.
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::{Arc, Barrier};
    use std::thread;

    fn temporary_ledger(label: &str) -> PathBuf {
        let mut random = [0u8; 16];
        getrandom::fill(&mut random).unwrap();
        let suffix = random
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect::<String>();
        std::env::temp_dir().join(format!("aspis-{label}-{}-{suffix}", std::process::id()))
    }

    fn copy_inactive_sum(
        values: &[aspis_core::field::QM31],
        masks: &[u16; 64],
    ) -> aspis_core::field::QM31 {
        values
            .iter()
            .copied()
            .enumerate()
            .filter(|(row, _)| masks[row >> 4] & (1 << (row & 15)) == 0)
            .fold(aspis_core::field::QM31::ZERO, |sum, (_, value)| {
                sum.add(value)
            })
    }

    #[test]
    fn pool_attempt_typestates_build_masks_and_variant_balanced_d() {
        let transfer_nonce = [0x41; 32];
        let transfer_context =
            StateOnlyHidingContext::pool_v1_private_transfer([0x73; 32], transfer_nonce);
        let transfer_attempt = StateOnlyAttemptSecrets::deterministic_spend_fixture(
            transfer_nonce,
            [0x31; 32],
            [0x51; 32],
        );
        let mut transfer_store =
            crate::state_only_hiding::InMemoryStateOnlyMaskNonceStore::default();
        let (transfer_reserved, _material) = transfer_attempt
            .reserve_and_build_pool_v1_private_transfer_mask_material_v1(
                crate::HOST_HASH,
                [0x21; 32],
                transfer_context,
                &mut transfer_store,
            )
            .unwrap();
        let transfer_salt = transfer_reserved
            .derive_pool_v1_leaf_salt(crate::HOST_HASH, transfer_context, 0x76, 7)
            .unwrap();
        assert_eq!(
            transfer_salt,
            transfer_reserved
                .derive_pool_v1_leaf_salt(crate::HOST_HASH, transfer_context, 0x76, 7)
                .unwrap(),
        );
        assert_ne!(
            transfer_salt,
            transfer_reserved
                .derive_pool_v1_leaf_salt(crate::HOST_HASH, transfer_context, 0x77, 7)
                .unwrap(),
        );
        assert_eq!(
            transfer_reserved
                .derive_pool_v1_leaf_salt(
                    crate::HOST_HASH,
                    StateOnlyHidingContext::pool_v1_withdrawal([0x73; 32], transfer_nonce),
                    0x76,
                    7,
                )
                .unwrap_err(),
            StateOnlyMaskBuildError::Layout,
        );
        assert_eq!(
            transfer_reserved
                .derive_pool_v1_leaf_salt(
                    crate::HOST_HASH,
                    StateOnlyHidingContext::pool_v1_private_transfer([0x74; 32], transfer_nonce,),
                    0x76,
                    7,
                )
                .unwrap_err(),
            StateOnlyMaskBuildError::Layout,
        );
        assert_eq!(
            transfer_reserved
                .derive_pool_v1_leaf_salt(
                    crate::HOST_HASH,
                    StateOnlyHidingContext::atomic_spend_v3([0x73; 32], transfer_nonce),
                    0x76,
                    7,
                )
                .unwrap_err(),
            StateOnlyMaskBuildError::Layout,
        );
        let transfer_d = transfer_reserved
            .derive_pool_v1_private_transfer_zero_factor_d(crate::HOST_HASH, transfer_context)
            .unwrap();
        assert_eq!(transfer_d.len(), STATE_ONLY_POSEIDON_TRACE_ROWS);
        assert_eq!(
            copy_inactive_sum(
                &transfer_d,
                pool_v1_private_transfer_copy_active_row_masks_compiled_v1(),
            ),
            aspis_core::field::QM31::ZERO,
        );
        assert_eq!(
            transfer_reserved
                .derive_pool_v1_withdrawal_zero_factor_d(crate::HOST_HASH, transfer_context)
                .unwrap_err(),
            StateOnlyMaskBuildError::Layout,
        );

        let withdrawal_nonce = [0x42; 32];
        let withdrawal_context =
            StateOnlyHidingContext::pool_v1_withdrawal([0x73; 32], withdrawal_nonce);
        let withdrawal_attempt = StateOnlyAttemptSecrets::deterministic_spend_fixture(
            withdrawal_nonce,
            [0x32; 32],
            [0x52; 32],
        );
        let mut withdrawal_store =
            crate::state_only_hiding::InMemoryStateOnlyMaskNonceStore::default();
        let (withdrawal_reserved, _material) = withdrawal_attempt
            .reserve_and_build_pool_v1_withdrawal_mask_material_v1(
                crate::HOST_HASH,
                [0x22; 32],
                withdrawal_context,
                &mut withdrawal_store,
            )
            .unwrap();
        assert!(withdrawal_reserved
            .derive_pool_v1_leaf_salt(crate::HOST_HASH, withdrawal_context, 0x76, 7)
            .is_ok());
        let withdrawal_d = withdrawal_reserved
            .derive_pool_v1_withdrawal_zero_factor_d(crate::HOST_HASH, withdrawal_context)
            .unwrap();
        assert_eq!(withdrawal_d.len(), STATE_ONLY_POSEIDON_TRACE_ROWS);
        assert_eq!(
            copy_inactive_sum(
                &withdrawal_d,
                pool_v1_withdrawal_copy_active_row_masks_compiled_v1(),
            ),
            aspis_core::field::QM31::ZERO,
        );

        let forest_nonce = [0x48; 32];
        let forest_context =
            StateOnlyHidingContext::pool_v1_pair_forest_v1([0x73; 32], forest_nonce);
        let forest_attempt = StateOnlyAttemptSecrets::deterministic_spend_fixture(
            forest_nonce,
            [0x38; 32],
            [0x58; 32],
        );
        let mut forest_store = crate::state_only_hiding::InMemoryStateOnlyMaskNonceStore::default();
        let (forest_reserved, _material) = forest_attempt
            .reserve_and_build_pool_v1_pair_forest_mask_material_v1(
                crate::HOST_HASH,
                [0x28; 32],
                forest_context,
                &mut forest_store,
            )
            .unwrap();
        assert!(forest_reserved
            .derive_pool_v1_leaf_salt(crate::HOST_HASH, forest_context, 0x76, 7)
            .is_ok());
        let forest_d = forest_reserved
            .derive_pool_v1_pair_forest_zero_factor_d(crate::HOST_HASH, forest_context)
            .unwrap();
        let forest_active = pool_v1_pair_forest_copy_active_row_masks_v1().unwrap();
        assert_eq!(forest_d.len(), STATE_ONLY_POSEIDON_TRACE_ROWS);
        assert_eq!(
            copy_inactive_sum(&forest_d, &forest_active),
            aspis_core::field::QM31::ZERO,
        );
        assert_eq!(
            forest_reserved
                .derive_pool_v1_private_transfer_zero_factor_d(crate::HOST_HASH, forest_context)
                .unwrap_err(),
            StateOnlyMaskBuildError::Layout,
        );
        assert_ne!(transfer_d, withdrawal_d);
        assert_ne!(transfer_d, forest_d);
    }

    #[test]
    fn os_attempt_separates_field_and_leaf_domains() {
        let attempt = StateOnlyAttemptSecrets::generate().unwrap();
        let nonce = attempt.mask_nonce();
        assert_ne!(nonce, [0; 32]);
        let context = StateOnlyHidingContext::atomic_v3([0x11; 32], nonce);
        let mut store = crate::state_only_hiding::InMemoryStateOnlyMaskNonceStore::default();
        let (attempt, _material) = attempt
            .reserve_and_build_atomic_mask_material_v3(
                crate::HOST_HASH,
                [0x21; 32],
                context,
                &mut store,
            )
            .unwrap();
        let a = attempt
            .derive_profile21_leaf_salt(crate::HOST_HASH, context, 1, 7)
            .unwrap();
        let b = attempt
            .derive_profile21_leaf_salt(crate::HOST_HASH, context, 2, 7)
            .unwrap();
        let c = attempt
            .derive_profile21_leaf_salt(crate::HOST_HASH, context, 1, 8)
            .unwrap();
        let profile22 = attempt
            .derive_profile22_leaf_salt(crate::HOST_HASH, context, 1, 7)
            .unwrap();
        assert_ne!(a, b);
        assert_ne!(a, c);
        assert_ne!(b, c);
        assert_ne!(a, profile22);
        let (x, f) = attempt
            .derive_profile21_source_masks(crate::HOST_HASH, context)
            .unwrap();
        let (x_again, f_again) = attempt
            .derive_profile21_source_masks(crate::HOST_HASH, context)
            .unwrap();
        assert_eq!(x, x_again);
        assert_eq!(f, f_again);
        assert_ne!(x, f);
        assert!(x
            .iter()
            .all(|value| *value != aspis_core::field::QM31::ZERO));

        let wrong_context = StateOnlyHidingContext::atomic_v3([0x11; 32], [0x99; 32]);
        assert_eq!(
            attempt
                .derive_profile21_leaf_salt(crate::HOST_HASH, wrong_context, 1, 7)
                .unwrap_err(),
            StateOnlyMaskBuildError::Layout
        );
    }

    #[test]
    fn durable_ledger_burns_nonce_across_reopen_and_statements() {
        let directory = temporary_ledger("nonce-reopen");
        let nonce = [0xa5; 32];
        let mut first = DurableStateOnlyMaskNonceStore::open(&directory).unwrap();
        assert!(first.reserve([1; 32], nonce));
        assert_eq!(first.last_error(), None);
        drop(first);

        let mut reopened = DurableStateOnlyMaskNonceStore::open(&directory).unwrap();
        assert!(!reopened.reserve([1; 32], nonce));
        assert!(!reopened.reserve([2; 32], nonce));
        assert_eq!(reopened.last_error(), None);
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn concurrent_reservation_has_exactly_one_winner() {
        let directory = temporary_ledger("nonce-race");
        fs::create_dir_all(&directory).unwrap();
        let barrier = Arc::new(Barrier::new(3));
        let mut handles = Vec::new();
        for statement in [[3u8; 32], [4u8; 32]] {
            let directory = directory.clone();
            let barrier = Arc::clone(&barrier);
            handles.push(thread::spawn(move || {
                let mut store = DurableStateOnlyMaskNonceStore::open(directory).unwrap();
                barrier.wait();
                store.reserve(statement, [0x7b; 32])
            }));
        }
        barrier.wait();
        let winners = handles
            .into_iter()
            .map(|handle| handle.join().unwrap())
            .filter(|won| *won)
            .count();
        assert_eq!(winners, 1);
        fs::remove_dir_all(directory).unwrap();
    }
}

fn profile21_source_expander_block(hash: HashFn, seed: [u8;32], counter: u64) -> [u8;32] {
    hash(&[PROFILE21_SOURCE_EXPAND_DOMAIN, &seed, &counter.to_le_bytes()])
}

#[cfg(kani)]
mod prover_commit_rom {
    use super::*;
    use crate::prover_commit_oracle as rom;

    #[kani::proof]
    #[kani::unwind(516)]
    #[kani::stub(crate::host_hashv, rom::query)]
    fn source_block() {
        rom::reset(2);
        let seed: [u8; 32] = kani::any();
        let counter: u64 = kani::any();
        assert_eq!(profile21_source_expander_block(crate::HOST_HASH, seed, counter),
            crate::HOST_HASH(&[b"aspis:state-only:profile21:source-expand:v1", &seed, &counter.to_le_bytes()]));
    }

    #[kani::proof]
    #[kani::unwind(516)]
    #[kani::stub(crate::host_hashv, rom::query)]
    fn source_next_word() {
        rom::reset(2);
        let seed: [u8; 32] = kani::any();
        let counter: u64 = kani::any();
        let block: [u8; 32] = kani::any();
        let word: usize = kani::any();
        kani::assume(word <= 8);
        let mut actual = Profile21SourceExpander { hash: crate::HOST_HASH, seed: Zeroizing::new(seed), counter, block, word };
        let (expected_block, expected_counter, slot) = if word == 8 {
            (crate::HOST_HASH(&[b"aspis:state-only:profile21:source-expand:v1", &seed, &counter.to_le_bytes()]), counter.wrapping_add(1), 0)
        } else { (block, counter, word) };
        let offset = 4 * slot;
        let expected = u32::from_le_bytes([expected_block[offset], expected_block[offset+1], expected_block[offset+2], expected_block[offset+3]]);
        assert_eq!(actual.next_word(), expected);
        assert_eq!(actual.block, expected_block);
        assert_eq!(actual.counter, expected_counter);
        assert_eq!(actual.word, slot + 1);
        assert_eq!(*actual.seed, seed);
    }

    #[kani::proof]
    #[kani::unwind(516)]
    #[kani::stub(crate::host_hashv, rom::query)]
    fn pool_binding() {
        rom::reset(2);
        let binding: [u8; 32] = kani::any();
        let context = StateOnlyHidingContext { statement_digest: kani::any(), mask_nonce: kani::any(), mask_layout_fingerprint: kani::any(), layout_factor_fingerprint: kani::any() };
        let mut encoded = [0u8; 81];
        encoded[0] = 1;
        encoded[1..33].copy_from_slice(&context.statement_digest);
        encoded[33..65].copy_from_slice(&context.mask_nonce);
        encoded[65..73].copy_from_slice(&context.mask_layout_fingerprint.to_le_bytes());
        encoded[73..81].copy_from_slice(&context.layout_factor_fingerprint.to_le_bytes());
        let expected = crate::HOST_HASH(&[
            b"aspis:state-only:pool-v1:private-attempt-binding:v1", &binding, &encoded,
            b"profile=pool-v1-tag73;generators=H26,G27,D28;factorD=0;rows=1024;c1=16;selected=28;theta=29;queries=16;first-cap=203",
        ]);
        assert_eq!(pool_v1_private_attempt_binding(crate::HOST_HASH, &binding, context), expected);
    }
    #[kani::proof]
    #[kani::unwind(516)]
    #[kani::stub(crate::host_hashv, rom::query)]
    fn pool_leaf_salt() {
        rom::reset(4);
        let nonce: [u8; 32] = kani::any();
        let binding: [u8; 32] = kani::any();
        let secret: [u8; 32] = kani::any();
        let tag: u8 = kani::any();
        let index: u32 = kani::any();
        let context = StateOnlyHidingContext {
            statement_digest: kani::any(), mask_nonce: nonce,
            mask_layout_fingerprint: PINNED_POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_FINGERPRINT_V1,
            layout_factor_fingerprint: PINNED_POOL_V1_PAIR_FOREST_HIDING_LAYOUT_FACTOR_FINGERPRINT_V1,
        };
        let reserved = ReservedStateOnlyAttemptSecrets {
            mask_nonce: nonce, precommit_binding: binding, reserved_context: context,
            leaf_salt_seed: Zeroizing::new(secret), source_mask_seed: Zeroizing::new(kani::any()),
        };
        let mut encoded = [0u8; 81];
        encoded[0] = 1;
        encoded[1..33].copy_from_slice(&context.statement_digest);
        encoded[33..65].copy_from_slice(&nonce);
        encoded[65..73].copy_from_slice(&0xf9daf3d54f4285d1u64.to_le_bytes());
        encoded[73..81].copy_from_slice(&0x698bcdedff44a4dbu64.to_le_bytes());
        let attempt = crate::HOST_HASH(&[
            b"aspis:state-only:pool-v1:private-attempt-binding:v1", &binding, &encoded,
            b"profile=pool-v1-tag73;generators=H26,G27,D28;factorD=0;rows=1024;c1=16;selected=28;theta=29;queries=16;first-cap=203",
        ]);
        let expected = crate::HOST_HASH(&[
            b"aspis:state-only:private-leaf-salt:v1", &attempt, &nonce, &[tag], &index.to_le_bytes(), &secret,
        ]);
        assert_eq!(reserved.derive_pool_v1_leaf_salt(crate::HOST_HASH, context, tag, index), Ok(expected));
    }

    // Exact m31 try body, with its return carried as an absorbing result.
    // The source m31 body is pinned and checked by harness/check-step-source.py.
    #[kani::proof]
    #[kani::unwind(516)]
    #[kani::stub(crate::host_hashv, rom::query)]
    fn source_try_step() {
        rom::reset(2);
        let seed: [u8; 32] = kani::any();
        let counter: u64 = kani::any();
        let block: [u8; 32] = kani::any();
        let word: usize = kani::any();
        kani::assume(word <= 8);
        let successful: bool = kani::any();
        let value: u32 = kani::any();
        kani::assume(value < aspis_core::field::P);
        let result = if successful { Ok(aspis_core::field::M31(value)) }
            else { Err(StateOnlyMaskBuildError::MaskSampleExhausted) };
        let state = crate::prover_commit_reference::State { seed, counter, block, word };
        let (expected, after) = crate::prover_commit_reference::try_step(
            crate::HOST_HASH, b"aspis:state-only:profile21:source-expand:v1", state, result);
        let mut actual = Profile21SourceExpander { hash: crate::HOST_HASH, seed: Zeroizing::new(seed), counter, block, word };
        let observed = match result {
            Ok(value) => Ok(value),
            Err(_) => {
                let candidate = actual.next_word() & 0x7fff_ffff;
                if candidate < aspis_core::field::P {
                    Ok(aspis_core::field::M31(candidate))
                } else { Err(StateOnlyMaskBuildError::MaskSampleExhausted) }
            }
        };
        assert_eq!(observed, expected);
        assert_eq!(*actual.seed, after.seed);
        assert_eq!(actual.counter, after.counter);
        assert_eq!(actual.block, after.block);
        assert_eq!(actual.word, after.word);
        assert!(actual.word <= 8);
    }

    #[kani::proof]
    #[kani::unwind(516)]
    #[kani::stub(crate::host_hashv, rom::query)]
    fn source_limb() {
        // At most three fresh blocks per side from any valid word slot.
        rom::reset(6);
        let seed: [u8; 32] = kani::any();
        let counter: u64 = kani::any();
        let block: [u8; 32] = kani::any();
        let word: usize = kani::any();
        kani::assume(word <= 8);
        let state = crate::prover_commit_reference::State { seed, counter, block, word };
        let (expected, after) = crate::prover_commit_reference::limb(crate::HOST_HASH, b"aspis:state-only:profile21:source-expand:v1", state);
        let mut actual = Profile21SourceExpander { hash: crate::HOST_HASH, seed: Zeroizing::new(seed), counter, block, word };
        assert_eq!(actual.m31(), expected);
        assert_eq!(*actual.seed, after.seed);
        assert_eq!(actual.counter, after.counter);
        assert_eq!(actual.block, after.block);
        assert_eq!(actual.word, after.word);
    }

}

#[cfg(kani)]
mod prover_commit_caller7 {
    use super::*;
    use crate::prover_commit_oracle as rom;
    #[kani::proof]
    #[kani::unwind(84)]
    #[kani::stub(crate::host_hashv, rom::expander_query)]
    #[kani::stub_verified(Profile21SourceExpander::next_word)]
    fn source_limb_caller() {
        let seed: [u8;32] = kani::any();
        let counter: u64 = kani::any();
        let block: [u8;32] = kani::any();
        let word: usize = kani::any();
        kani::assume(word <= 8);
        rom::reset_expander(b"aspis:state-only:profile21:source-expand:v1", seed, counter);
        let state = crate::prover_commit_reference::State { seed, counter, block, word };
        let (expected, after) = crate::prover_commit_reference::limb_caller(
            crate::HOST_HASH, b"aspis:state-only:profile21:source-expand:v1", state);
        let mut actual = Profile21SourceExpander { hash: crate::HOST_HASH, seed: Zeroizing::new(seed), counter, block, word };
        assert_eq!(actual.m31(), expected);
        assert_eq!(*actual.seed, after.seed);
        assert_eq!(actual.counter, after.counter);
        assert_eq!(actual.block, after.block);
        assert_eq!(actual.word, after.word);
    }
    #[kani::proof]
    #[kani::unwind(84)]
    #[kani::stub(crate::host_hashv, rom::expander_query)]
    #[kani::stub_verified(rom::expander_query)]
    fn source_qm31_caller() {
        let seed: [u8;32] = kani::any();
        let counter: u64 = kani::any();
        let block: [u8;32] = kani::any();
        let word: usize = kani::any();
        kani::assume(word <= 8);
        rom::reset_expander(b"aspis:state-only:profile21:source-expand:v1", seed, counter);
        let state = crate::prover_commit_reference::State { seed, counter, block, word };
        let (expected, after) = crate::prover_commit_reference::qm31_caller(
            crate::HOST_HASH, b"aspis:state-only:profile21:source-expand:v1", state);
        let mut actual = Profile21SourceExpander { hash: crate::HOST_HASH, seed: Zeroizing::new(seed), counter, block, word };
        assert_eq!(actual.qm31(), expected);
        assert_eq!(*actual.seed, after.seed);
        assert_eq!(actual.counter, after.counter);
        assert_eq!(actual.block, after.block);
        assert_eq!(actual.word, after.word);
    }
    #[kani::proof_for_contract(Profile21SourceExpander::next_word)]
    #[kani::unwind(84)]
    #[kani::stub(crate::host_hashv, rom::expander_query)]
    fn source_next_contract() {
        let seed: [u8;32] = kani::any();
        let base_counter: u64 = kani::any();
        let counter: u64 = kani::any();
        let block: [u8;32] = kani::any();
        let word: usize = kani::any();
        kani::assume(word <= 8);
        kani::assume(word < 8 || counter.wrapping_sub(base_counter) < 9);
        rom::reset_expander(b"aspis:state-only:profile21:source-expand:v1", seed, base_counter);
        let mut actual = Profile21SourceExpander { hash: crate::HOST_HASH, seed: Zeroizing::new(seed), counter, block, word };
        let _ = actual.next_word();
    }


}

/// Universal four-call control-flow comparison over an arbitrary scalar trace.
/// Stubs are relational inputs, not asserted scalar contracts. Each side sees
/// the same trace; all sampled results and successor states are unconstrained.
#[cfg(kani)]
mod prover_commit_four8 {
    use super::*;
    use aspis_core::field::{M31, QM31};
    use crate::prover_commit_reference::State;
    type Sample = Result<M31, StateOnlyMaskBuildError>;
    const ZERO: State = State { seed: [0;32], counter: 0, block: [0;32], word: 0 };
    static mut STATES: [State;4] = [ZERO;4];
    static mut VALUES: [Sample;4] = [Ok(M31::ZERO);4];
    static mut CURSOR: usize = 0;
    fn transition() -> (Sample, State) {
        unsafe {
            assert!(CURSOR < 4);
            let pair = (VALUES[CURSOR], STATES[CURSOR]);
            CURSOR += 1;
            pair
        }
    }
    fn shipped_scalar(state: &mut Profile21SourceExpander) -> Sample {
        let (value, after) = transition();
        *state.seed = after.seed;
        state.counter = after.counter;
        state.block = after.block;
        state.word = after.word;
        value
    }
    fn reference_scalar(_: aspis_core::HashFn, _: &[u8], _: State) -> (Sample, State) {
        transition()
    }
    #[kani::proof]
    #[kani::unwind(34)]
    #[kani::stub(Profile21SourceExpander::m31, shipped_scalar)]
    #[kani::stub(crate::prover_commit_reference::limb_caller, reference_scalar)]
    fn four_control() {
        for i in 0..4 {
            unsafe {
                STATES[i] = kani::any();
                VALUES[i] = if kani::any::<bool>() { Ok(M31(kani::any())) }
                    else { Err(StateOnlyMaskBuildError::MaskSampleExhausted) };
            }
        }
        let state: State = kani::any();
        unsafe { CURSOR = 0; }
        let (expected, after) = crate::prover_commit_reference::qm31_caller(
            crate::HOST_HASH, b"unused relational input", state);
        let expected_calls = unsafe { CURSOR };
        unsafe { CURSOR = 0; }
        let mut actual = Profile21SourceExpander { hash: crate::HOST_HASH,
            seed: Zeroizing::new(state.seed), counter: state.counter, block: state.block, word: state.word };
        let observed: Result<QM31, StateOnlyMaskBuildError> = actual.qm31();
        assert_eq!(observed, expected);
        assert_eq!(*actual.seed, after.seed);
        assert_eq!(actual.counter, after.counter);
        assert_eq!(actual.block, after.block);
        assert_eq!(actual.word, after.word);
        assert_eq!(unsafe { CURSOR }, expected_calls);
    }
}

#[cfg(kani)]
#[path="state_only_entropy_prover_rw_kani.rs"]
mod prover_rw_kani;

// Local native contracts for the frozen entropy owner. These harnesses are
// absent from ordinary builds and make no claim about RNG distributions.
#[cfg(kani)]
mod prover_rw_entropy_native_contracts {
    use super::*;

    fn nonzero_kernel(bytes:&[u8;32])->bool {
        let a=u64::from_le_bytes([bytes[0],bytes[1],bytes[2],bytes[3],bytes[4],bytes[5],bytes[6],bytes[7]]);
        let b=u64::from_le_bytes([bytes[8],bytes[9],bytes[10],bytes[11],bytes[12],bytes[13],bytes[14],bytes[15]]);
        let c=u64::from_le_bytes([bytes[16],bytes[17],bytes[18],bytes[19],bytes[20],bytes[21],bytes[22],bytes[23]]);
        let d=u64::from_le_bytes([bytes[24],bytes[25],bytes[26],bytes[27],bytes[28],bytes[29],bytes[30],bytes[31]]);
        (a|b|c|d)!=0
    }

    static mut REPLIES: [[u8; 64]; 16] = [[0; 64]; 16];
    static mut FAILURES: u16 = 0;
    static mut PARTIAL: [u8; 16] = [0; 16];
    static mut ERROR_WORDS: [i32; 16] = [1; 16];
    static mut CALLS: usize = 0;

    // All nonzero representations of the Linux getrandom error carrier.
    // Transmute is confined to this harness; size is checked by rustc and the
    // type's sole validity restriction is its NonZeroI32 field.
    fn error(word: i32) -> getrandom::Error {
        let raw = core::num::NonZeroI32::new(word)
            .unwrap_or(core::num::NonZeroI32::new(1).unwrap());
        unsafe { core::mem::transmute(raw) }
    }

    fn fill(destination: &mut [u8]) -> Result<(), getrandom::Error> {
        let call = unsafe { CALLS };
        assert!(call < 16);
        assert_eq!(destination.len(), 64);
        assert!(destination.iter().all(|byte| *byte == 0));
        unsafe { CALLS = call + 1; }
        let failed = (unsafe { FAILURES } & (1u16 << call)) != 0;
        // A completely arbitrary post-fill buffer includes every partial
        // error-write pattern; the caller cannot distinguish how it arose.
        destination.copy_from_slice(&unsafe { REPLIES[call] });
        if failed { Err(error(unsafe { ERROR_WORDS[call] })) } else { Ok(()) }
    }

    fn initialize(replies: [[u8; 64]; 16], failures: u16, error_words: [i32; 16]) {
        unsafe {
            REPLIES = replies;
            FAILURES = failures;
            PARTIAL = kani::any();
            ERROR_WORDS = error_words;
            CALLS = 0;
        }
    }

    // This parameterization covers every rejected full reply: at least one
    // half is zero, and the other half is unrestricted. No law on the tape
    // distribution, inter-call independence or provider availability is used.
    fn rejected_prefix(replies: &mut [[u8; 64]; 16], count: usize) {
        for reply in replies.iter_mut().take(count) { *reply = bad_reply(*reply); }
    }

    fn first_success<const LOW: usize, const HIGH: usize>() {
        let index: usize = kani::any();
        kani::assume(LOW <= index && index < HIGH);
        let nonce: [u8; 32] = kani::any();
        kani::assume(nonce.iter().any(|byte| *byte != 0));
        let mut replies: [[u8; 64]; 16] = kani::any();
        rejected_prefix(&mut replies, index);
        kani::assume(replies[index][..32].iter().any(|byte| *byte != 0));
        kani::assume(replies[index][32..].iter().any(|byte| *byte != 0));
        let through = if index == 15 { u16::MAX } else { (1u16 << (index + 1)) - 1 };
        let failures: u16 = kani::any::<u16>() & !through;
        initialize(replies, failures, kani::any());
        match StateOnlyAttemptSecrets::generate_for_mask_nonce(nonce) {
            Ok(secret) => {
                assert_eq!(secret.mask_nonce, nonce);
                assert_eq!(&secret.field_mask_entropy[..], &replies[index][..32]);
                assert_eq!(&secret.leaf_salt_seed[..], &replies[index][32..]);
            }
            Err(_) => assert!(false, "first accepted reply must be returned"),
        }
        assert_eq!(unsafe { CALLS }, index + 1);
    }

    fn first_error<const LOW: usize, const HIGH: usize>() {
        let index: usize = kani::any();
        kani::assume(LOW <= index && index < HIGH);
        let nonce: [u8; 32] = kani::any();
        kani::assume(nonce.iter().any(|byte| *byte != 0));
        let mut replies: [[u8; 64]; 16] = kani::any();
        rejected_prefix(&mut replies, index);
        let failures = (kani::any::<u16>() & !((1u16 << index) - 1)) | (1u16 << index);
        let errors: [i32; 16] = kani::any();
        initialize(replies, failures, errors);
        match StateOnlyAttemptSecrets::generate_for_mask_nonce(nonce) {
            Err(StateOnlyAttemptEntropyError::Os(actual)) => assert_eq!(actual, error(errors[index])),
            _ => assert!(false, "first provider error must preserve its payload"),
        }
        assert_eq!(unsafe { CALLS }, index + 1);
    }

    #[kani::proof]
    #[kani::unwind(65)]
    #[kani::stub(super::entropy_nonzero32, nonzero_kernel)]
    #[kani::stub(getrandom::fill, fill)]
    fn success_0_3() { first_success::<0, 4>(); }
    #[kani::proof]
    #[kani::unwind(65)]
    #[kani::stub(super::entropy_nonzero32, nonzero_kernel)]
    #[kani::stub(getrandom::fill, fill)]
    fn success_4_7() { first_success::<4, 8>(); }
    #[kani::proof]
    #[kani::unwind(65)]
    #[kani::stub(super::entropy_nonzero32, nonzero_kernel)]
    #[kani::stub(getrandom::fill, fill)]
    fn success_8_11() { first_success::<8, 12>(); }
    #[kani::proof]
    #[kani::unwind(65)]
    #[kani::stub(super::entropy_nonzero32, nonzero_kernel)]
    #[kani::stub(getrandom::fill, fill)]
    fn success_12_15() { first_success::<12, 16>(); }
    #[kani::proof]
    #[kani::unwind(65)]
    #[kani::stub(super::entropy_nonzero32, nonzero_kernel)]
    #[kani::stub(getrandom::fill, fill)]
    fn error_0_3() { first_error::<0, 4>(); }
    #[kani::proof]
    #[kani::unwind(65)]
    #[kani::stub(super::entropy_nonzero32, nonzero_kernel)]
    #[kani::stub(getrandom::fill, fill)]
    fn error_4_7() { first_error::<4, 8>(); }
    #[kani::proof]
    #[kani::unwind(65)]
    #[kani::stub(super::entropy_nonzero32, nonzero_kernel)]
    #[kani::stub(getrandom::fill, fill)]
    fn error_8_11() { first_error::<8, 12>(); }
    #[kani::proof]
    #[kani::unwind(65)]
    #[kani::stub(super::entropy_nonzero32, nonzero_kernel)]
    #[kani::stub(getrandom::fill, fill)]
    fn error_12_15() { first_error::<12, 16>(); }

    #[kani::proof]
    #[kani::unwind(65)]
    #[kani::stub(super::entropy_nonzero32, nonzero_kernel)]
    #[kani::stub(getrandom::fill, fill)]
    fn exhausted_sixteen() {
        let nonce: [u8; 32] = kani::any();
        kani::assume(nonce.iter().any(|byte| *byte != 0));
        let mut replies: [[u8; 64]; 16] = kani::any();
        rejected_prefix(&mut replies, 16);
        initialize(replies, 0, kani::any());
        assert!(matches!(StateOnlyAttemptSecrets::generate_for_mask_nonce(nonce),
            Err(StateOnlyAttemptEntropyError::RepeatedZeroBlock)));
        assert_eq!(unsafe { CALLS }, 16);
    }

    #[kani::proof]
    #[kani::unwind(65)]
    #[kani::stub(super::entropy_nonzero32, nonzero_kernel)]
    #[kani::stub(getrandom::fill, fill)]
    fn zero_nonce_no_callback() {
        initialize(kani::any(), kani::any(), kani::any());
        assert!(matches!(StateOnlyAttemptSecrets::generate_for_mask_nonce([0; 32]),
            Err(StateOnlyAttemptEntropyError::RepeatedZeroBlock)));
        assert_eq!(unsafe { CALLS }, 0);
    }

    #[kani::proof]
    fn zeroizing64_native_abi() {
        assert_eq!(core::mem::size_of::<Zeroizing<[u8; 64]>>(), 64);
        assert_eq!(core::mem::align_of::<Zeroizing<[u8; 64]>>(), 1);
    }

    #[kani::proof]
    #[kani::unwind(65)]
    fn zeroizing64_native_drop_at_byte() {
        let bytes: [u8; 64] = kani::any();
        let byte: usize = usize::from(kani::any::<u8>() & 63);
        let mut storage = core::mem::MaybeUninit::new(Zeroizing::new(bytes));
        let pointer = storage.as_mut_ptr();
        unsafe {
            core::ptr::drop_in_place(pointer);
            // Read initialized raw bytes in retained MaybeUninit storage,
            // without reconstituting or accessing a dropped owner value.
            let after = pointer.cast::<u8>().add(byte).read();
            assert_eq!(after, 0);
        }
    }

    #[kani::proof]
    #[kani::unwind(33)]
    fn zeroizing32_native_drop() {
        let bytes: [u8; 32] = kani::any();
        assert_eq!(core::mem::size_of::<Zeroizing<[u8; 32]>>(), 32);
        assert_eq!(core::mem::align_of::<Zeroizing<[u8; 32]>>(), 1);
        let mut storage = core::mem::MaybeUninit::new(Zeroizing::new(bytes));
        let pointer = storage.as_mut_ptr();
        unsafe {
            core::ptr::drop_in_place(pointer);
            let after = pointer.cast::<[u8; 32]>().read();
            assert_eq!(after, [0; 32]);
        }
    }

    static mut SMALL_REPLIES: [[u8; 64]; 2] = [[0; 64]; 2];
    static mut SMALL_FAIL_AT: usize = 2;
    static mut SMALL_ERROR: i32 = 1;
    static mut SMALL_PARTIAL: u8 = 0;
    static mut SMALL_CALLS: usize = 0;

    fn small_fill(destination: &mut [u8]) -> Result<(), getrandom::Error> {
        let call = unsafe { SMALL_CALLS };
        assert!(call < 2);
        assert_eq!(destination.len(), 64);
        assert!(destination.iter().all(|byte| *byte == 0));
        unsafe { SMALL_CALLS = call + 1; }
        let failed = call == unsafe { SMALL_FAIL_AT };
        destination.copy_from_slice(&unsafe { SMALL_REPLIES[call] });
        if failed { Err(error(unsafe { SMALL_ERROR })) } else { Ok(()) }
    }

    fn small_setup(replies: [[u8; 64]; 2], fail_at: usize, error_word: i32) {
        unsafe {
            SMALL_REPLIES = replies;
            SMALL_FAIL_AT = fail_at;
            SMALL_ERROR = error_word;
            SMALL_PARTIAL = kani::any();
            SMALL_CALLS = 0;
        }
    }

    fn bad_reply(mut reply: [u8; 64]) -> [u8; 64] {
        if kani::any::<bool>() { reply[..32].fill(0); }
        else { reply[32..].fill(0); }
        reply
    }

    #[kani::proof]
    #[kani::unwind(65)]
    #[kani::stub(super::entropy_nonzero32, nonzero_kernel)]
    #[kani::stub(getrandom::fill, small_fill)]
    fn first_error_compact() {
        let nonce: [u8; 32] = kani::any();
        kani::assume(nonce != [0; 32]);
        let replies: [[u8; 64]; 2] = kani::any();
        let code: i32 = kani::any();
        small_setup(replies, 0, code);
        match StateOnlyAttemptSecrets::generate_for_mask_nonce(nonce) {
            Err(StateOnlyAttemptEntropyError::Os(actual)) => assert_eq!(actual, error(code)),
            _ => assert!(false),
        }
        assert_eq!(unsafe { SMALL_CALLS }, 1);
    }

    #[kani::proof]
    #[kani::unwind(65)]
    #[kani::stub(super::entropy_nonzero32, nonzero_kernel)]
    #[kani::stub(getrandom::fill, small_fill)]
    fn first_success_compact() {
        let nonce: [u8; 32] = kani::any();
        kani::assume(nonce != [0; 32]);
        let replies: [[u8; 64]; 2] = kani::any();
        kani::assume(replies[0][..32].iter().any(|byte| *byte != 0));
        kani::assume(replies[0][32..].iter().any(|byte| *byte != 0));
        small_setup(replies, 2, kani::any());
        let secret = StateOnlyAttemptSecrets::generate_for_mask_nonce(nonce).unwrap();
        assert_eq!(secret.mask_nonce, nonce);
        assert_eq!(&secret.field_mask_entropy[..], &replies[0][..32]);
        assert_eq!(&secret.leaf_salt_seed[..], &replies[0][32..]);
        assert_eq!(unsafe { SMALL_CALLS }, 1);
    }

    #[kani::proof]
    #[kani::unwind(65)]
    #[kani::stub(super::entropy_nonzero32, nonzero_kernel)]
    #[kani::stub(getrandom::fill, small_fill)]
    fn error_after_one_rejection() {
        let nonce: [u8; 32] = kani::any();
        kani::assume(nonce != [0; 32]);
        let first = bad_reply(kani::any());
        let code: i32 = kani::any();
        small_setup([first, kani::any()], 1, code);
        match StateOnlyAttemptSecrets::generate_for_mask_nonce(nonce) {
            Err(StateOnlyAttemptEntropyError::Os(actual)) => assert_eq!(actual, error(code)),
            _ => assert!(false),
        }
        assert_eq!(unsafe { SMALL_CALLS }, 2);
    }

    #[kani::proof]
    #[kani::unwind(65)]
    #[kani::stub(super::entropy_nonzero32, nonzero_kernel)]
    #[kani::stub(getrandom::fill, small_fill)]
    fn success_after_one_rejection() {
        let nonce: [u8; 32] = kani::any();
        kani::assume(nonce != [0; 32]);
        let first = bad_reply(kani::any());
        let last: [u8; 64] = kani::any();
        kani::assume(last[..32].iter().any(|byte| *byte != 0));
        kani::assume(last[32..].iter().any(|byte| *byte != 0));
        small_setup([first, last], 2, kani::any());
        let secret = StateOnlyAttemptSecrets::generate_for_mask_nonce(nonce).unwrap();
        assert_eq!(secret.mask_nonce, nonce);
        assert_eq!(&secret.field_mask_entropy[..], &last[..32]);
        assert_eq!(&secret.leaf_salt_seed[..], &last[32..]);
        assert_eq!(unsafe { SMALL_CALLS }, 2);
    }

    fn zero_fill(destination: &mut [u8]) -> Result<(), getrandom::Error> {
        assert_eq!(destination.len(), 64);
        assert!(destination.iter().all(|byte| *byte == 0));
        unsafe { SMALL_CALLS += 1; }
        Ok(())
    }

    #[kani::proof]
    #[kani::unwind(65)]
    #[kani::stub(super::entropy_nonzero32, nonzero_kernel)]
    #[kani::stub(getrandom::fill, zero_fill)]
    fn zero_tape_cap() {
        let nonce: [u8; 32] = kani::any();
        kani::assume(nonce != [0; 32]);
        unsafe { SMALL_CALLS = 0; }
        assert!(matches!(StateOnlyAttemptSecrets::generate_for_mask_nonce(nonce),
            Err(StateOnlyAttemptEntropyError::RepeatedZeroBlock)));
        assert_eq!(unsafe { SMALL_CALLS }, 16);
    }

    #[kani::proof]
    #[kani::unwind(65)]
    fn error_abi_and_from() {
        assert_eq!(core::mem::size_of::<getrandom::Error>(), 4);
        assert_eq!(core::mem::align_of::<getrandom::Error>(), 4);
        let raw = core::num::NonZeroI32::new(kani::any())
            .unwrap_or(core::num::NonZeroI32::new(1).unwrap());
        let input = error(raw.get());
        let after: core::num::NonZeroI32 = unsafe { core::mem::transmute(input) };
        assert_eq!(after, raw);
        match StateOnlyAttemptEntropyError::from(input) {
            StateOnlyAttemptEntropyError::Os(value) => assert_eq!(value, input),
            _ => assert!(false),
        }
    }

    #[kani::proof]
    #[kani::unwind(65)]
    fn zeroizing64_borrow_writeback() {
        let initial: [u8; 64] = kani::any();
        let replacement: [u8; 64] = kani::any();
        let mut owner = Zeroizing::new(initial);
        assert_eq!(*owner, initial);
        {
            let view: &mut [u8] = owner.as_mut();
            assert_eq!(view.len(), 64);
            view.copy_from_slice(&replacement);
        }
        assert_eq!(*owner, replacement);
    }

    #[kani::proof]
    #[kani::unwind(65)]
    fn attempt_owner_drop_frame() {
        let nonce: [u8; 32] = kani::any();
        let value = StateOnlyAttemptSecrets {
            mask_nonce: nonce,
            field_mask_entropy: Zeroizing::new(kani::any()),
            leaf_salt_seed: Zeroizing::new(kani::any()),
        };
        let mut storage = core::mem::MaybeUninit::new(value);
        let pointer = storage.as_mut_ptr();
        unsafe {
            let public = core::ptr::addr_of!((*pointer).mask_nonce);
            let field = core::ptr::addr_of!((*pointer).field_mask_entropy).cast::<[u8; 32]>();
            let leaf = core::ptr::addr_of!((*pointer).leaf_salt_seed).cast::<[u8; 32]>();
            core::ptr::drop_in_place(pointer);
            assert_eq!(public.read(), nonce);
            assert_eq!(field.read(), [0; 32]);
            assert_eq!(leaf.read(), [0; 32]);
        }
    }

    #[kani::proof]
    #[kani::unwind(65)]
    #[kani::stub(super::entropy_nonzero32, nonzero_kernel)]
    #[kani::stub(getrandom::fill, fill)]
    fn all_terminal_positions() {
        let index = usize::from(kani::any::<u8>() & 15);
        let is_error: bool = kani::any();
        let nonce: [u8; 32] = kani::any();
        kani::assume(nonce != [0; 32]);
        let mut replies: [[u8; 64]; 16] = kani::any();
        rejected_prefix(&mut replies, index);
        if !is_error {
            kani::assume(replies[index][..32].iter().any(|byte| *byte != 0));
            kani::assume(replies[index][32..].iter().any(|byte| *byte != 0));
        }
        let before = (1u16 << index) - 1;
        let mut failures: u16 = kani::any::<u16>() & !before;
        if is_error { failures |= 1u16 << index; }
        else { failures &= !(1u16 << index); }
        let codes: [i32; 16] = kani::any();
        initialize(replies, failures, codes);
        match StateOnlyAttemptSecrets::generate_for_mask_nonce(nonce) {
            Ok(secret) => {
                assert!(!is_error);
                assert_eq!(secret.mask_nonce, nonce);
                assert_eq!(&secret.field_mask_entropy[..], &replies[index][..32]);
                assert_eq!(&secret.leaf_salt_seed[..], &replies[index][32..]);
            }
            Err(StateOnlyAttemptEntropyError::Os(value)) => {
                assert!(is_error);
                assert_eq!(value, error(codes[index]));
            }
            Err(_) => assert!(false),
        }
        assert_eq!(unsafe { CALLS }, index + 1);
    }
}

// Split native support contracts; absent from all production builds.
#[cfg(kani)]
#[path="state_only_entropy_prover_rw_stream_kani.rs"]
mod prover_rw_stream_kani;
