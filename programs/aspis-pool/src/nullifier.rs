//! Canonical Pool V1 nullifier-marker planning.
//!
//! This module validates the exact writable marker PDA and distinguishes the
//! two admissible fresh account forms from an occupied marker. It performs no
//! System CPI or account write. The entrypoint's atomic spend composition
//! rechecks the plan after proof verification, creates/allocates if required,
//! acquires every Pool/history mutable borrow, and only then copies the
//! prevalidated fixed marker image.

use aspis_statement::{
    decode_digest_canonical,
    pool_v1::{
        decode_pool_v1_nullifier_marker, encode_pool_v1_nullifier_marker, PoolV1NullifierMarkerV1,
        POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES, POOL_V1_NULLIFIER_MARKER_SEED,
    },
};
use solana_program::{account_info::AccountInfo, program_error::ProgramError, pubkey::Pubkey};
use solana_sdk_ids::system_program;

use crate::error::PoolV1ProgramError;

/// Exact third seed validation is part of this address API: arbitrary 32 bytes
/// that do not decode as eight canonical M31 limbs are rejected before PDA
/// derivation.
pub fn pool_v1_nullifier_marker_address(
    program_id: &Pubkey,
    pool: &Pubkey,
    canonical_nullifier_encoding: &[u8; 32],
) -> Result<(Pubkey, u8), ProgramError> {
    decode_digest_canonical(canonical_nullifier_encoding)
        .map_err(|_| PoolV1ProgramError::InvalidNullifierMarkerAccount)?;
    Ok(Pubkey::find_program_address(
        &[
            POOL_V1_NULLIFIER_MARKER_SEED,
            pool.as_ref(),
            canonical_nullifier_encoding,
        ],
        program_id,
    ))
}

/// Domain tag of the pair-forest (R1) marker seed digest (B1, 2026-10-19).
pub const POOL_V1_PAIR_FOREST_MARKER_SEED_DOMAIN: &[u8; 20] = b"aspis-marker-seed-v1";
/// Length of the `create_with_seed` seed string (`MAX_SEED_LEN`).
pub const POOL_V1_PAIR_FOREST_MARKER_SEED_BYTES: usize = 32;

/// Pack the first 28 bytes (224 bits) of `digest` into 32 seven-bit bytes.
///
/// The 224 bits are read big-endian (most significant bit of `digest[0]`
/// first) and cut into 32 consecutive 7-bit groups; group `i` becomes
/// `seed[i]`, so every byte is in `0x00..=0x7f` and the result is valid
/// UTF-8 (ASCII) of exactly 32 bytes. Bytes `digest[28..32]` are discarded.
pub fn pack_pool_v1_pair_forest_marker_seed_v1(digest: &[u8; 32]) -> [u8; 32] {
    let mut seed = [0u8; POOL_V1_PAIR_FOREST_MARKER_SEED_BYTES];
    let mut chunk = 0;
    while chunk < 4 {
        let mut word = 0u64;
        let mut byte = 0;
        while byte < 7 {
            word = (word << 8) | u64::from(digest[7 * chunk + byte]);
            byte += 1;
        }
        let mut group = 0;
        while group < 8 {
            seed[8 * chunk + group] = ((word >> (7 * (7 - group))) & 0x7f) as u8;
            group += 1;
        }
        chunk += 1;
    }
    seed
}

/// B1 marker seed: 7-bit packing of the first 28 bytes of
/// `SHA-256("aspis-marker-seed-v1" || pool || canonical nullifier)`.
pub fn pool_v1_pair_forest_marker_seed_v1(
    pool: &Pubkey,
    canonical_nullifier_encoding: &[u8; 32],
) -> [u8; 32] {
    let digest = solana_program::hash::hashv(&[
        POOL_V1_PAIR_FOREST_MARKER_SEED_DOMAIN,
        pool.as_ref(),
        canonical_nullifier_encoding,
    ])
    .to_bytes();
    pack_pool_v1_pair_forest_marker_seed_v1(&digest)
}

/// The packed seed as the `&str` the System program's `*_with_seed`
/// instructions take. Every byte is below 0x80, so this never fails for a
/// seed produced by [`pack_pool_v1_pair_forest_marker_seed_v1`].
pub fn pool_v1_pair_forest_marker_seed_str_v1(seed: &[u8; 32]) -> Result<&str, ProgramError> {
    core::str::from_utf8(seed).map_err(|_| PoolV1ProgramError::InvalidNullifierMarkerAddress.into())
}

/// Canonical pair-forest (R1) nullifier-marker address (B1).
///
/// `address = create_with_seed(master, seed, program_id)` with
/// `seed = pool_v1_pair_forest_marker_seed_v1(master, nullifier)`. The base is
/// the forest master PDA (`["aspis-pair-forest-master-v1", mint]`, bump stored
/// at master byte 7), which the Pool authenticates by its stored bump and
/// signs for with `invoke_signed`. There is no bump and no search. Returns the
/// address and the 32-byte seed. Non-canonical nullifier encodings are
/// rejected before hashing, as for the legacy PDA marker.
pub fn pool_v1_pair_forest_nullifier_marker_address(
    program_id: &Pubkey,
    master: &Pubkey,
    canonical_nullifier_encoding: &[u8; 32],
) -> Result<(Pubkey, [u8; 32]), ProgramError> {
    decode_digest_canonical(canonical_nullifier_encoding)
        .map_err(|_| PoolV1ProgramError::InvalidNullifierMarkerAccount)?;
    let seed = pool_v1_pair_forest_marker_seed_v1(master, canonical_nullifier_encoding);
    let address = Pubkey::create_with_seed(
        master,
        pool_v1_pair_forest_marker_seed_str_v1(&seed)?,
        program_id,
    )
    .map_err(|_| PoolV1ProgramError::InvalidNullifierMarkerAddress)?;
    Ok((address, seed))
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NullifierMarkerPreparationV1 {
    /// A data-empty System-owned PDA. Future composition must perform the
    /// reviewed create/allocate/assign sequence with `invoke_signed`.
    CreateOrAllocateSystemOwned,
    /// An exact-size, program-owned, all-zero account ready for the final copy.
    PopulateProgramOwnedZeroed,
}

/// Fully validated but unapplied marker plan.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PlannedNullifierMarkerV1 {
    preparation: NullifierMarkerPreparationV1,
    address_bump: u8,
    marker: PoolV1NullifierMarkerV1,
    encoded_marker: [u8; POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES],
}

impl PlannedNullifierMarkerV1 {
    pub(crate) fn preparation(self) -> NullifierMarkerPreparationV1 {
        self.preparation
    }

    pub(crate) fn address_bump(self) -> u8 {
        self.address_bump
    }

    pub(crate) fn marker(self) -> PoolV1NullifierMarkerV1 {
        self.marker
    }

    pub(crate) fn encoded_marker(self) -> [u8; POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES] {
        self.encoded_marker
    }
}

/// Plan consumption of one exact canonical nullifier marker without writing.
///
/// A valid occupied marker always returns `NullifierAlreadyConsumed`, even if
/// its recorded context differs. This prevents a hypothetical PDA collision
/// or pre-existing valid marker from being overwritten. Nonzero bytes that do
/// not decode as the exact Pool V1 marker format are malformed and fail
/// separately.
pub fn plan_nullifier_marker_consumption_v1(
    program_id: &Pubkey,
    marker_account: &AccountInfo,
    marker: PoolV1NullifierMarkerV1,
) -> Result<PlannedNullifierMarkerV1, ProgramError> {
    let encoded_marker = encode_pool_v1_nullifier_marker(&marker)
        .map_err(|_| PoolV1ProgramError::InvalidNullifierMarkerAccount)?;
    let pool = Pubkey::new_from_array(marker.pool);
    let canonical_nullifier = marker.canonical_nullifier_encoding();
    let (expected_address, address_bump) =
        pool_v1_nullifier_marker_address(program_id, &pool, &canonical_nullifier)?;
    if marker_account.key != &expected_address || marker_account.key == &pool {
        return Err(PoolV1ProgramError::InvalidNullifierMarkerAddress.into());
    }
    let preparation = classify_nullifier_marker_account_v1(program_id, marker_account)?;
    Ok(PlannedNullifierMarkerV1 {
        preparation,
        address_bump,
        marker,
        encoded_marker,
    })
}

/// Privilege, owner and image classification shared by both marker address
/// schemes. The caller has already authenticated the account key.
fn classify_nullifier_marker_account_v1(
    program_id: &Pubkey,
    marker_account: &AccountInfo,
) -> Result<NullifierMarkerPreparationV1, ProgramError> {
    if marker_account.executable || marker_account.is_signer || !marker_account.is_writable {
        return Err(PoolV1ProgramError::InvalidNullifierMarkerAccount.into());
    }
    if marker_account.owner == program_id {
        let data = marker_account.try_borrow_data()?;
        if data.len() != POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES {
            return Err(PoolV1ProgramError::InvalidNullifierMarkerAccount.into());
        }
        if data.iter().all(|byte| *byte == 0) {
            Ok(NullifierMarkerPreparationV1::PopulateProgramOwnedZeroed)
        } else if decode_pool_v1_nullifier_marker(&data).is_ok() {
            Err(PoolV1ProgramError::NullifierAlreadyConsumed.into())
        } else {
            Err(PoolV1ProgramError::InvalidNullifierMarkerAccount.into())
        }
    } else if marker_account.owner == &system_program::id() && marker_account.data_is_empty() {
        Ok(NullifierMarkerPreparationV1::CreateOrAllocateSystemOwned)
    } else {
        Err(PoolV1ProgramError::InvalidNullifierMarkerAccount.into())
    }
}

/// Fully validated but unapplied pair-forest (B1) marker plan.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PlannedPairForestNullifierMarkerV1 {
    preparation: NullifierMarkerPreparationV1,
    seed: [u8; 32],
    encoded_marker: [u8; POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES],
}

impl PlannedPairForestNullifierMarkerV1 {
    pub(crate) fn preparation(self) -> NullifierMarkerPreparationV1 {
        self.preparation
    }

    pub(crate) fn seed(&self) -> &[u8; 32] {
        &self.seed
    }

    pub(crate) fn encoded_marker(self) -> [u8; POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES] {
        self.encoded_marker
    }
}

/// Plan consumption of the one pair-forest marker of `marker.nullifier`.
///
/// The address is `pool_v1_pair_forest_nullifier_marker_address(program_id,
/// marker.pool, nullifier)`: one SHA-256 for the seed and one for the address,
/// no curve test and no bump. Replay detection, the error codes and the image
/// checks are those of the legacy PDA marker: a valid occupied marker returns
/// `NullifierAlreadyConsumed`.
pub fn plan_pair_forest_nullifier_marker_consumption_v1(
    program_id: &Pubkey,
    marker_account: &AccountInfo,
    marker: PoolV1NullifierMarkerV1,
) -> Result<PlannedPairForestNullifierMarkerV1, ProgramError> {
    let encoded_marker = encode_pool_v1_nullifier_marker(&marker)
        .map_err(|_| PoolV1ProgramError::InvalidNullifierMarkerAccount)?;
    let pool = Pubkey::new_from_array(marker.pool);
    let (expected_address, seed) = pool_v1_pair_forest_nullifier_marker_address(
        program_id,
        &pool,
        &marker.canonical_nullifier_encoding(),
    )?;
    if marker_account.key != &expected_address || marker_account.key == &pool {
        return Err(PoolV1ProgramError::InvalidNullifierMarkerAddress.into());
    }
    let preparation = classify_nullifier_marker_account_v1(program_id, marker_account)?;
    Ok(PlannedPairForestNullifierMarkerV1 {
        preparation,
        seed,
        encoded_marker,
    })
}

/// Re-classify the already address-authenticated marker after the System
/// CPI. The key cannot change, so no address is derived again.
pub(crate) fn recheck_pair_forest_nullifier_marker_v1(
    program_id: &Pubkey,
    marker_account: &AccountInfo,
) -> Result<NullifierMarkerPreparationV1, ProgramError> {
    classify_nullifier_marker_account_v1(program_id, marker_account)
}

#[cfg(test)]
mod tests {
    use aspis_core::field::{M31, P};
    use aspis_statement::{
        pool_v1::{PoolV1TransitionKind, POOL_V1_NULLIFIER_MARKER_MAGIC},
        poseidon2::Digest,
    };
    use solana_program::clock::Epoch;

    use super::*;

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + 19 * index as u32))
    }

    fn marker(pool: Pubkey) -> PoolV1NullifierMarkerV1 {
        PoolV1NullifierMarkerV1 {
            transition_kind: PoolV1TransitionKind::PrivateTransfer,
            pool: pool.to_bytes(),
            deployment_domain: [2u8; 32],
            nullifier: digest(10),
            retained_anchor_sequence: 44,
            retained_anchor_root: digest(100),
            verifier_profile: [3u8; 32],
            verifier_release: [4u8; 32],
        }
    }

    fn account<'a>(
        key: &'a Pubkey,
        owner: &'a Pubkey,
        lamports: &'a mut u64,
        data: &'a mut [u8],
        signer: bool,
        writable: bool,
        executable: bool,
    ) -> AccountInfo<'a> {
        AccountInfo::new(
            key,
            signer,
            writable,
            lamports,
            data,
            owner,
            executable,
            Epoch::default(),
        )
    }

    fn hex32(text: &str) -> [u8; 32] {
        core::array::from_fn(|i| u8::from_str_radix(&text[2 * i..2 * i + 2], 16).unwrap())
    }

    fn le_limbs(limbs: [u32; 8]) -> [u8; 32] {
        let mut out = [0u8; 32];
        for (i, limb) in limbs.iter().enumerate() {
            out[4 * i..4 * i + 4].copy_from_slice(&limb.to_le_bytes());
        }
        out
    }

    /// Bit-by-bit reference for the 7-bit packing (independent of the
    /// word-wise production loop).
    fn reference_pack(digest: &[u8; 32]) -> [u8; 32] {
        let bit = |k: usize| (digest[k / 8] >> (7 - k % 8)) & 1;
        core::array::from_fn(|i| (0..7).fold(0u8, |acc, j| (acc << 1) | bit(7 * i + j)))
    }

    struct SplitMix(u64);
    impl SplitMix {
        fn next(&mut self) -> u64 {
            self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
            let mut z = self.0;
            z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
            z ^ (z >> 31)
        }
        fn bytes32(&mut self) -> [u8; 32] {
            let mut out = [0u8; 32];
            for chunk in out.chunks_mut(8) {
                chunk.copy_from_slice(&self.next().to_le_bytes());
            }
            out
        }
        fn canonical_nullifier(&mut self) -> [u8; 32] {
            le_limbs(core::array::from_fn(|_| (self.next() % u64::from(P)) as u32))
        }
    }

    #[test]
    fn b1_marker_seed_and_address_match_fixed_vectors() {
        // Vectors computed independently with Python hashlib (SHA-256) and a
        // big-integer 7-bit split of the first 28 digest bytes.
        let program_id = Pubkey::new_from_array([0x11; 32]);
        let master = Pubkey::new_from_array([0x22; 32]);
        let nullifier = le_limbs([1, 2, 3, 4, 5, 6, 7, 8]);
        let seed = pool_v1_pair_forest_marker_seed_v1(&master, &nullifier);
        assert_eq!(
            seed,
            hex32("217964665252030d613d413c1737232007756c6f6a6264480071683c72265b7d")
        );
        let (address, returned_seed) =
            pool_v1_pair_forest_nullifier_marker_address(&program_id, &master, &nullifier)
                .unwrap();
        assert_eq!(returned_seed, seed);
        assert_eq!(
            address.to_bytes(),
            hex32("86774708d96c52689a57843643ab11e5ebafb7f999e45817017c24a9f91a2fba")
        );

        let program_id = Pubkey::new_from_array(core::array::from_fn(|i| i as u8));
        let master = Pubkey::new_from_array(core::array::from_fn(|i| 32 + i as u8));
        let nullifier = le_limbs(core::array::from_fn(|i| 0x7fff_fffe - i as u32));
        let (address, seed) =
            pool_v1_pair_forest_nullifier_marker_address(&program_id, &master, &nullifier)
                .unwrap();
        assert_eq!(
            seed,
            hex32("6f046b26057d4727644415796c6719403510732a4a190c7e49655f15431b1269")
        );
        assert_eq!(
            address.to_bytes(),
            hex32("d7ccb51c6b2c9b4e312c0dee424b5d197bdbcee3c4d4474c6de43a341b99e3f0")
        );

        assert_eq!(
            pack_pool_v1_pair_forest_marker_seed_v1(&[0xff; 32]),
            [0x7f; 32]
        );
        let mut top = [0u8; 32];
        top[0] = 0x80;
        let mut expected = [0u8; 32];
        expected[0] = 0x40;
        assert_eq!(pack_pool_v1_pair_forest_marker_seed_v1(&top), expected);
        // Bytes 28..32 of the digest are not used.
        let mut tail = [0u8; 32];
        tail[28..].fill(0xff);
        assert_eq!(pack_pool_v1_pair_forest_marker_seed_v1(&tail), [0u8; 32]);
    }

    #[test]
    fn b1_packed_seed_is_32_byte_utf8_and_address_is_create_with_seed_for_random_inputs() {
        use sha2::{Digest as _, Sha256};
        let mut rng = SplitMix(0xa5b1_5eed);
        let mut seen = std::collections::BTreeSet::new();
        for round in 0..20_000 {
            let digest = rng.bytes32();
            let packed = pack_pool_v1_pair_forest_marker_seed_v1(&digest);
            assert_eq!(packed, reference_pack(&digest));
            let text = core::str::from_utf8(&packed).expect("valid UTF-8");
            assert_eq!(text.len(), 32);
            assert!(packed.iter().all(|byte| *byte < 0x80));

            let program_id = Pubkey::new_from_array(rng.bytes32());
            let master = Pubkey::new_from_array(rng.bytes32());
            let nullifier = rng.canonical_nullifier();
            let (address, seed) =
                pool_v1_pair_forest_nullifier_marker_address(&program_id, &master, &nullifier)
                    .unwrap();
            let seed_digest: [u8; 32] = Sha256::new()
                .chain_update(POOL_V1_PAIR_FOREST_MARKER_SEED_DOMAIN)
                .chain_update(master.as_ref())
                .chain_update(nullifier)
                .finalize()
                .into();
            assert_eq!(seed, reference_pack(&seed_digest));
            assert!(core::str::from_utf8(&seed).is_ok_and(|text| text.len() == 32));
            let independent: [u8; 32] = Sha256::new()
                .chain_update(master.as_ref())
                .chain_update(seed)
                .chain_update(program_id.as_ref())
                .finalize()
                .into();
            assert_eq!(address.to_bytes(), independent);
            assert_eq!(
                Pubkey::create_with_seed(&master, core::str::from_utf8(&seed).unwrap(), &program_id)
                    .unwrap(),
                address
            );
            if round < 5_000 {
                assert!(seen.insert(seed), "seed collision in a 5,000 sample");
            }
        }
    }

    #[test]
    fn b1_plan_accepts_only_the_seed_address_under_the_master_base() {
        let program_id = Pubkey::new_unique();
        let pool = Pubkey::new_unique();
        let marker = marker(pool);
        let nullifier = marker.canonical_nullifier_encoding();
        let (marker_key, seed) =
            pool_v1_pair_forest_nullifier_marker_address(&program_id, &pool, &nullifier).unwrap();
        let seed_text = core::str::from_utf8(&seed).unwrap();
        let mut other_seed = seed;
        other_seed[31] ^= 1;
        let candidates = [
            // Wrong authority (base): an attacker can create Pool-owned
            // accounts at its own base's seed addresses.
            Pubkey::create_with_seed(&Pubkey::new_unique(), seed_text, &program_id).unwrap(),
            // Wrong seed under the right base.
            Pubkey::create_with_seed(
                &pool,
                core::str::from_utf8(&other_seed).unwrap(),
                &program_id,
            )
            .unwrap(),
            // Right base and seed, wrong owner program in the derivation.
            Pubkey::create_with_seed(&pool, seed_text, &Pubkey::new_unique()).unwrap(),
            // The legacy canonical PDA marker address.
            pool_v1_nullifier_marker_address(&program_id, &pool, &nullifier)
                .unwrap()
                .0,
        ];
        for key in candidates {
            let mut lamports = rent_exempt();
            let mut zeroed = [0u8; POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES];
            let forged = account(&key, &program_id, &mut lamports, &mut zeroed, false, true, false);
            assert_eq!(
                plan_pair_forest_nullifier_marker_consumption_v1(&program_id, &forged, marker),
                Err(PoolV1ProgramError::InvalidNullifierMarkerAddress.into())
            );
        }

        // The right address, prefunded but owned by someone else.
        let foreign_owner = Pubkey::new_unique();
        let mut lamports = rent_exempt();
        let mut zeroed = [0u8; POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES];
        let foreign = account(
            &marker_key,
            &foreign_owner,
            &mut lamports,
            &mut zeroed,
            false,
            true,
            false,
        );
        assert_eq!(
            plan_pair_forest_nullifier_marker_consumption_v1(&program_id, &foreign, marker),
            Err(PoolV1ProgramError::InvalidNullifierMarkerAccount.into())
        );
        // Signer or read-only marker accounts.
        for (signer, writable) in [(true, true), (false, false)] {
            let mut lamports = 0;
            let mut empty = [];
            let system = system_program::id();
            let bad = account(&marker_key, &system, &mut lamports, &mut empty, signer, writable, false);
            assert_eq!(
                plan_pair_forest_nullifier_marker_consumption_v1(&program_id, &bad, marker),
                Err(PoolV1ProgramError::InvalidNullifierMarkerAccount.into())
            );
        }
        // Fresh (System-owned empty, with or without lamports) plans creation;
        // a consumed image at the address is `NullifierAlreadyConsumed`.
        for prefund in [0u64, 1, rent_exempt()] {
            let mut lamports = prefund;
            let mut empty = [];
            let system = system_program::id();
            let fresh = account(&marker_key, &system, &mut lamports, &mut empty, false, true, false);
            let plan =
                plan_pair_forest_nullifier_marker_consumption_v1(&program_id, &fresh, marker)
                    .unwrap();
            assert_eq!(
                plan.preparation(),
                NullifierMarkerPreparationV1::CreateOrAllocateSystemOwned
            );
            assert_eq!(plan.seed(), &seed);
        }
        let mut consumed = encode_pool_v1_nullifier_marker(&marker).unwrap();
        let mut lamports = rent_exempt();
        let occupied = account(&marker_key, &program_id, &mut lamports, &mut consumed, false, true, false);
        assert_eq!(
            plan_pair_forest_nullifier_marker_consumption_v1(&program_id, &occupied, marker),
            Err(PoolV1ProgramError::NullifierAlreadyConsumed.into())
        );
    }

    fn rent_exempt() -> u64 {
        solana_program::rent::Rent::default()
            .minimum_balance(POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES)
    }

    #[test]
    fn exact_seed_schedule_uses_pool_and_canonical_nullifier_bytes() {
        let program_id = Pubkey::new_unique();
        let pool = Pubkey::new_unique();
        let marker = marker(pool);
        let nullifier = marker.canonical_nullifier_encoding();
        let derived = pool_v1_nullifier_marker_address(&program_id, &pool, &nullifier).unwrap();
        assert_eq!(
            derived,
            Pubkey::find_program_address(
                &[POOL_V1_NULLIFIER_MARKER_SEED, pool.as_ref(), &nullifier],
                &program_id
            )
        );

        let mut noncanonical = nullifier;
        noncanonical[..4].copy_from_slice(&P.to_le_bytes());
        assert_eq!(
            pool_v1_nullifier_marker_address(&program_id, &pool, &noncanonical),
            Err(PoolV1ProgramError::InvalidNullifierMarkerAccount.into())
        );
    }

    #[test]
    fn system_empty_and_program_zeroed_accounts_produce_distinct_unapplied_plans() {
        let program_id = Pubkey::new_unique();
        let pool = Pubkey::new_unique();
        let marker = marker(pool);
        let marker_key = pool_v1_nullifier_marker_address(
            &program_id,
            &pool,
            &marker.canonical_nullifier_encoding(),
        )
        .unwrap()
        .0;

        let mut system_lamports = 7;
        let mut empty_data = [];
        let system_owner = system_program::id();
        let system_account = account(
            &marker_key,
            &system_owner,
            &mut system_lamports,
            &mut empty_data,
            false,
            true,
            false,
        );
        let system_plan =
            plan_nullifier_marker_consumption_v1(&program_id, &system_account, marker).unwrap();
        assert_eq!(
            system_plan.preparation,
            NullifierMarkerPreparationV1::CreateOrAllocateSystemOwned
        );
        assert_eq!(
            &system_plan.encoded_marker[..4],
            &POOL_V1_NULLIFIER_MARKER_MAGIC
        );

        let mut program_lamports = 1;
        let mut zeroed = [0u8; POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES];
        let program_account = account(
            &marker_key,
            &program_id,
            &mut program_lamports,
            &mut zeroed,
            false,
            true,
            false,
        );
        let program_plan =
            plan_nullifier_marker_consumption_v1(&program_id, &program_account, marker).unwrap();
        assert_eq!(
            program_plan.preparation,
            NullifierMarkerPreparationV1::PopulateProgramOwnedZeroed
        );
        assert_eq!(system_plan.encoded_marker, program_plan.encoded_marker);
        assert!(zeroed.iter().all(|byte| *byte == 0));
    }

    #[test]
    fn fresh_program_marker_can_be_consumed_once_and_second_plan_rejects() {
        let program_id = Pubkey::new_unique();
        let pool = Pubkey::new_unique();
        let marker = marker(pool);
        let marker_key = pool_v1_nullifier_marker_address(
            &program_id,
            &pool,
            &marker.canonical_nullifier_encoding(),
        )
        .unwrap()
        .0;
        let mut lamports = 1;
        let mut data = [0u8; POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES];
        let plan = {
            let account = account(
                &marker_key,
                &program_id,
                &mut lamports,
                &mut data,
                false,
                true,
                false,
            );
            plan_nullifier_marker_consumption_v1(&program_id, &account, marker).unwrap()
        };
        // This direct copy models only the later infallible persistence step;
        // no public writer is exposed by the production module.
        data.copy_from_slice(&plan.encoded_marker);
        let account = account(
            &marker_key,
            &program_id,
            &mut lamports,
            &mut data,
            false,
            true,
            false,
        );
        assert_eq!(
            plan_nullifier_marker_consumption_v1(&program_id, &account, marker),
            Err(PoolV1ProgramError::NullifierAlreadyConsumed.into())
        );
    }

    #[test]
    fn occupied_valid_marker_for_other_context_is_never_overwritten() {
        let program_id = Pubkey::new_unique();
        let pool = Pubkey::new_unique();
        let requested = marker(pool);
        let marker_key = pool_v1_nullifier_marker_address(
            &program_id,
            &pool,
            &requested.canonical_nullifier_encoding(),
        )
        .unwrap()
        .0;
        let occupied = PoolV1NullifierMarkerV1 {
            deployment_domain: [99u8; 32],
            ..requested
        };
        let mut data = encode_pool_v1_nullifier_marker(&occupied).unwrap();
        let before = data;
        let mut lamports = 1;
        let account = account(
            &marker_key,
            &program_id,
            &mut lamports,
            &mut data,
            false,
            true,
            false,
        );
        assert_eq!(
            plan_nullifier_marker_consumption_v1(&program_id, &account, requested),
            Err(PoolV1ProgramError::NullifierAlreadyConsumed.into())
        );
        assert_eq!(data, before);
    }

    #[test]
    fn wrong_address_owner_privileges_length_or_malformed_image_fail_closed() {
        let program_id = Pubkey::new_unique();
        let pool = Pubkey::new_unique();
        let marker = marker(pool);
        let marker_key = pool_v1_nullifier_marker_address(
            &program_id,
            &pool,
            &marker.canonical_nullifier_encoding(),
        )
        .unwrap()
        .0;

        let wrong_key = Pubkey::new_unique();
        let mut lamports = 1;
        let mut zeroed = [0u8; POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES];
        let wrong_address = account(
            &wrong_key,
            &program_id,
            &mut lamports,
            &mut zeroed,
            false,
            true,
            false,
        );
        assert_eq!(
            plan_nullifier_marker_consumption_v1(&program_id, &wrong_address, marker),
            Err(PoolV1ProgramError::InvalidNullifierMarkerAddress.into())
        );

        let foreign_owner = Pubkey::new_unique();
        let foreign = account(
            &marker_key,
            &foreign_owner,
            &mut lamports,
            &mut zeroed,
            false,
            true,
            false,
        );
        assert_eq!(
            plan_nullifier_marker_consumption_v1(&program_id, &foreign, marker),
            Err(PoolV1ProgramError::InvalidNullifierMarkerAccount.into())
        );

        let readonly = account(
            &marker_key,
            &program_id,
            &mut lamports,
            &mut zeroed,
            false,
            false,
            false,
        );
        assert_eq!(
            plan_nullifier_marker_consumption_v1(&program_id, &readonly, marker),
            Err(PoolV1ProgramError::InvalidNullifierMarkerAccount.into())
        );

        let mut wrong_length = [0u8; POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES - 1];
        let wrong_length_account = account(
            &marker_key,
            &program_id,
            &mut lamports,
            &mut wrong_length,
            false,
            true,
            false,
        );
        assert_eq!(
            plan_nullifier_marker_consumption_v1(&program_id, &wrong_length_account, marker),
            Err(PoolV1ProgramError::InvalidNullifierMarkerAccount.into())
        );

        zeroed[0] = 0xff;
        let before = zeroed;
        let malformed = account(
            &marker_key,
            &program_id,
            &mut lamports,
            &mut zeroed,
            false,
            true,
            false,
        );
        assert_eq!(
            plan_nullifier_marker_consumption_v1(&program_id, &malformed, marker),
            Err(PoolV1ProgramError::InvalidNullifierMarkerAccount.into())
        );
        assert_eq!(zeroed, before);
    }
}
