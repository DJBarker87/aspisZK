//! Zero-copy validation and mutation helpers for Pool V1 root pages.

use aspis_core::field::P;
use aspis_statement::{
    decode_digest_canonical, encode_digest_canonical,
    pool_v1::{
        root_history_location, POOL_V1_DIGEST_ENCODING_VERSION, POOL_V1_ROOT_HISTORY_CAPACITY,
        POOL_V1_ROOT_HISTORY_CAPACITY_LOG2, POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES,
        POOL_V1_ROOT_HISTORY_PAGE_MAGIC, POOL_V1_ROOT_HISTORY_PAGE_SEED,
        POOL_V1_ROOT_HISTORY_PAGE_VERSION,
    },
    poseidon2::Digest,
};
use solana_program::{account_info::AccountInfo, program_error::ProgramError, pubkey::Pubkey};

use crate::error::PoolV1ProgramError;

const PAGE_POOL_OFFSET: usize = 8;
const PAGE_NUMBER_OFFSET: usize = 40;
const PAGE_FIRST_SEQUENCE_OFFSET: usize = 48;
const PAGE_FILLED_OFFSET: usize = 56;
const PAGE_ROOTS_OFFSET: usize = 64;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RootPageHeaderV1 {
    pub pool: Pubkey,
    pub page_number: u64,
    pub first_sequence: u64,
    pub filled: u16,
}

pub fn pool_v1_root_page_address(
    program_id: &Pubkey,
    pool: &Pubkey,
    page_number: u64,
) -> (Pubkey, u8) {
    let page_number_bytes = page_number.to_le_bytes();
    Pubkey::find_program_address(
        &[
            POOL_V1_ROOT_HISTORY_PAGE_SEED,
            pool.as_ref(),
            &page_number_bytes,
        ],
        program_id,
    )
}

pub(crate) fn digest_is_canonical(digest: &Digest) -> bool {
    digest.iter().all(|limb| limb.0 < P)
}

/// Zero check of a region of a root history page: true iff every byte of
/// `data` is zero, and true for the empty region. It decides the same
/// predicate as `data.iter().all(|byte| *byte == 0)`.
///
/// Form: no loop. A non-empty region is all zero iff its first byte is zero
/// and every byte equals the byte after it, that is, iff the region without
/// its last byte equals the region without its first byte (slice equality on
/// two shared borrows of `data`, both of length `len - 1`).
pub(crate) fn page_bytes_are_zero(data: &[u8]) -> bool {
    data.is_empty() || (data[0] == 0 && data[..data.len() - 1] == data[1..])
}

pub(crate) fn require_program_account(
    account: &AccountInfo,
    program_id: &Pubkey,
    writable: bool,
) -> Result<(), ProgramError> {
    if account.owner != program_id {
        return Err(ProgramError::IncorrectProgramId);
    }
    if account.executable || account.is_writable != writable {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(())
}

pub(crate) fn require_program_owned(
    account: &AccountInfo,
    program_id: &Pubkey,
) -> Result<(), ProgramError> {
    if account.owner != program_id {
        return Err(ProgramError::IncorrectProgramId);
    }
    if account.executable {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(())
}

pub(crate) fn require_root_page_address(
    program_id: &Pubkey,
    pool: &Pubkey,
    page_number: u64,
    account: &AccountInfo,
) -> Result<(), ProgramError> {
    let expected = pool_v1_root_page_address(program_id, pool, page_number).0;
    if account.key != &expected {
        return Err(PoolV1ProgramError::InvalidRootPageAddress.into());
    }
    Ok(())
}

/// B4: authenticate an existing root page by a caller-supplied bump hint
/// with one `create_program_address`. Sound for pages that already exist,
/// because the Pool creates every page at the canonical bump (F6 of the PDA
/// study); a mismatch is the same `InvalidRootPageAddress` as before.
pub(crate) fn require_root_page_address_with_bump(
    program_id: &Pubkey,
    pool: &Pubkey,
    page_number: u64,
    bump: u8,
    account: &AccountInfo,
) -> Result<(), ProgramError> {
    let page_number_bytes = page_number.to_le_bytes();
    if !crate::registry::stored_bump_address_matches(
        &[
            POOL_V1_ROOT_HISTORY_PAGE_SEED,
            pool.as_ref(),
            &page_number_bytes,
            &[bump],
        ],
        program_id,
        account.key,
    ) {
        return Err(PoolV1ProgramError::InvalidRootPageAddress.into());
    }
    Ok(())
}

pub(crate) fn validate_root_page_bytes(
    data: &[u8],
    expected_pool: &Pubkey,
    expected_page_number: u64,
) -> Result<RootPageHeaderV1, ProgramError> {
    if data.len() != POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES
        || data[..4] != POOL_V1_ROOT_HISTORY_PAGE_MAGIC
        || data[4] != POOL_V1_ROOT_HISTORY_PAGE_VERSION
        || data[5] != POOL_V1_ROOT_HISTORY_CAPACITY_LOG2
        || data[6] != POOL_V1_DIGEST_ENCODING_VERSION
        || data[7] != 0
        || data[58..64] != [0u8; 6]
    {
        return Err(PoolV1ProgramError::InvalidAccountType.into());
    }
    let pool = Pubkey::new_from_array(
        data[PAGE_POOL_OFFSET..PAGE_NUMBER_OFFSET]
            .try_into()
            .unwrap(),
    );
    let page_number = u64::from_le_bytes(
        data[PAGE_NUMBER_OFFSET..PAGE_FIRST_SEQUENCE_OFFSET]
            .try_into()
            .unwrap(),
    );
    let first_sequence = u64::from_le_bytes(
        data[PAGE_FIRST_SEQUENCE_OFFSET..PAGE_FILLED_OFFSET]
            .try_into()
            .unwrap(),
    );
    let filled = u16::from_le_bytes(data[PAGE_FILLED_OFFSET..58].try_into().unwrap());
    let expected_first = page_number
        .checked_mul(POOL_V1_ROOT_HISTORY_CAPACITY as u64)
        .ok_or(PoolV1ProgramError::ArithmeticOverflow)?;
    if pool != *expected_pool
        || page_number != expected_page_number
        || first_sequence != expected_first
        || usize::from(filled) > POOL_V1_ROOT_HISTORY_CAPACITY
    {
        return Err(PoolV1ProgramError::StateHistoryMismatch.into());
    }
    for slot in 0..usize::from(filled) {
        let start = PAGE_ROOTS_OFFSET + slot * 32;
        decode_digest_canonical(data[start..start + 32].try_into().unwrap())
            .map_err(|_| ProgramError::InvalidAccountData)?;
    }
    let unused_start = PAGE_ROOTS_OFFSET + usize::from(filled) * 32;
    if !page_bytes_are_zero(&data[unused_start..]) {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(RootPageHeaderV1 {
        pool,
        page_number,
        first_sequence,
        filled,
    })
}

/// Audit-only hot decoder for a root page created and exclusively extended by
/// this Pool release. The ordinary decoder above remains mandatory for
/// untrusted/migration inputs. This retains the complete header/canonical
/// current-root checks at the caller; it omits only rescanning prior roots and
/// untouched zero capacity, which are inductive properties of the Pool's
/// initialize/append writers.
#[cfg(feature = "pair-forest-history-page-invariant-audit")]
pub(crate) fn validate_root_page_bytes_from_program_invariant(
    data: &[u8],
    expected_pool: &Pubkey,
    expected_page_number: u64,
) -> Result<RootPageHeaderV1, ProgramError> {
    if data.len() != POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES
        || data[..4] != POOL_V1_ROOT_HISTORY_PAGE_MAGIC
        || data[4] != POOL_V1_ROOT_HISTORY_PAGE_VERSION
        || data[5] != POOL_V1_ROOT_HISTORY_CAPACITY_LOG2
        || data[6] != POOL_V1_DIGEST_ENCODING_VERSION
        || data[7] != 0
        || data[58..64] != [0u8; 6]
    {
        return Err(PoolV1ProgramError::InvalidAccountType.into());
    }
    let pool = Pubkey::new_from_array(
        data[PAGE_POOL_OFFSET..PAGE_NUMBER_OFFSET]
            .try_into()
            .unwrap(),
    );
    let page_number = u64::from_le_bytes(
        data[PAGE_NUMBER_OFFSET..PAGE_FIRST_SEQUENCE_OFFSET]
            .try_into()
            .unwrap(),
    );
    let first_sequence = u64::from_le_bytes(
        data[PAGE_FIRST_SEQUENCE_OFFSET..PAGE_FILLED_OFFSET]
            .try_into()
            .unwrap(),
    );
    let filled = u16::from_le_bytes(data[PAGE_FILLED_OFFSET..58].try_into().unwrap());
    let expected_first = page_number
        .checked_mul(POOL_V1_ROOT_HISTORY_CAPACITY as u64)
        .ok_or(PoolV1ProgramError::ArithmeticOverflow)?;
    if pool != *expected_pool
        || page_number != expected_page_number
        || first_sequence != expected_first
        || usize::from(filled) > POOL_V1_ROOT_HISTORY_CAPACITY
    {
        return Err(PoolV1ProgramError::StateHistoryMismatch.into());
    }
    Ok(RootPageHeaderV1 {
        pool,
        page_number,
        first_sequence,
        filled,
    })
}

pub(crate) fn read_retained_root(
    data: &[u8],
    header: RootPageHeaderV1,
    sequence: u64,
) -> Result<Digest, ProgramError> {
    let location = root_history_location(sequence);
    if location.page_number != header.page_number || location.slot >= header.filled {
        return Err(PoolV1ProgramError::StateHistoryMismatch.into());
    }
    let start = PAGE_ROOTS_OFFSET + usize::from(location.slot) * 32;
    decode_digest_canonical(data[start..start + 32].try_into().unwrap())
        .map_err(|_| ProgramError::InvalidAccountData)
}

pub(crate) fn write_new_page_unchecked(
    data: &mut [u8],
    pool: &Pubkey,
    page_number: u64,
    first_sequence: u64,
    roots: &[Digest],
) {
    debug_assert_eq!(data.len(), POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES);
    debug_assert!(roots.len() <= POOL_V1_ROOT_HISTORY_CAPACITY);
    data.fill(0);
    data[..4].copy_from_slice(&POOL_V1_ROOT_HISTORY_PAGE_MAGIC);
    data[4] = POOL_V1_ROOT_HISTORY_PAGE_VERSION;
    data[5] = POOL_V1_ROOT_HISTORY_CAPACITY_LOG2;
    data[6] = POOL_V1_DIGEST_ENCODING_VERSION;
    data[PAGE_POOL_OFFSET..PAGE_NUMBER_OFFSET].copy_from_slice(pool.as_ref());
    data[PAGE_NUMBER_OFFSET..PAGE_FIRST_SEQUENCE_OFFSET]
        .copy_from_slice(&page_number.to_le_bytes());
    data[PAGE_FIRST_SEQUENCE_OFFSET..PAGE_FILLED_OFFSET]
        .copy_from_slice(&first_sequence.to_le_bytes());
    data[PAGE_FILLED_OFFSET..58].copy_from_slice(&(roots.len() as u16).to_le_bytes());
    for (slot, root) in roots.iter().enumerate() {
        let start = PAGE_ROOTS_OFFSET + slot * 32;
        data[start..start + 32].copy_from_slice(&encode_digest_canonical(root));
    }
}

pub(crate) fn append_roots_unchecked(data: &mut [u8], header: RootPageHeaderV1, roots: &[Digest]) {
    debug_assert!(usize::from(header.filled) + roots.len() <= POOL_V1_ROOT_HISTORY_CAPACITY);
    for (offset, root) in roots.iter().enumerate() {
        let slot = usize::from(header.filled) + offset;
        let start = PAGE_ROOTS_OFFSET + slot * 32;
        data[start..start + 32].copy_from_slice(&encode_digest_canonical(root));
    }
    let filled = header.filled + roots.len() as u16;
    data[PAGE_FILLED_OFFSET..58].copy_from_slice(&filled.to_le_bytes());
}

pub(crate) fn validate_new_page_account(
    program_id: &Pubkey,
    pool: &Pubkey,
    page_number: u64,
    account: &AccountInfo,
) -> Result<(), ProgramError> {
    require_program_account(account, program_id, true)?;
    require_root_page_address(program_id, pool, page_number, account)?;
    let data = account.try_borrow_data()?;
    if data.len() != POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES || !page_bytes_are_zero(&data) {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(())
}

#[cfg(all(test, feature = "pair-forest-history-page-invariant-audit"))]
mod invariant_tests {
    use super::*;
    use aspis_core::field::{M31, P};
    use aspis_statement::pool_v1::root_history::initialize_root_history_page_bytes_v1;
    use std::vec;
    use std::vec::Vec;

    fn root(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + index as u32))
    }

    #[test]
    fn invariant_header_matches_strict_writer_image_and_retains_current_root_teeth() {
        let pool = Pubkey::new_unique();
        let roots = (0..POOL_V1_ROOT_HISTORY_CAPACITY)
            .map(|index| root(100 + index as u32))
            .collect::<Vec<_>>();
        let mut data = vec![0u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES];
        initialize_root_history_page_bytes_v1(&mut data, pool.to_bytes(), 0, &roots).unwrap();
        let strict = validate_root_page_bytes(&data, &pool, 0).unwrap();
        let hot = validate_root_page_bytes_from_program_invariant(&data, &pool, 0).unwrap();
        assert_eq!(hot, strict);
        assert_eq!(read_retained_root(&data, hot, 255).unwrap(), roots[255]);

        let current = PAGE_ROOTS_OFFSET + 255 * 32;
        data[current..current + 4].copy_from_slice(&P.to_le_bytes());
        assert_eq!(
            read_retained_root(&data, hot, 255),
            Err(ProgramError::InvalidAccountData)
        );
    }

    #[test]
    fn invariant_decoder_boundary_is_prior_writer_history() {
        let pool = Pubkey::new_unique();
        let roots = [root(200), root(300)];
        let mut data = vec![0u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES];
        initialize_root_history_page_bytes_v1(&mut data, pool.to_bytes(), 0, &roots).unwrap();
        let prior = PAGE_ROOTS_OFFSET;
        data[prior..prior + 4].copy_from_slice(&P.to_le_bytes());
        assert!(validate_root_page_bytes(&data, &pool, 0).is_err());
        assert!(validate_root_page_bytes_from_program_invariant(&data, &pool, 0).is_ok());

        data[4] ^= 1;
        assert!(validate_root_page_bytes_from_program_invariant(&data, &pool, 0).is_err());
    }
}

/// Differential tests of `page_bytes_are_zero` against the byte-by-byte checks
/// it replaced, kept verbatim below as test-only oracles. On the host,
/// `sol_memcmp` runs the SDK's Rust stub, not the SBF syscall; the syscall is
/// exercised by the LiteSVM runs of the built ELF.
#[cfg(test)]
mod page_zero_check_tests {
    use super::*;
    use aspis_core::field::M31;
    use aspis_statement::pool_v1::root_history::initialize_root_history_page_bytes_v1;
    use solana_program::clock::Epoch;
    use std::vec;
    use std::vec::Vec;

    const PAGE: usize = POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES;

    // Oracle 1: the unused-tail check of `validate_root_page_bytes`, verbatim
    // (true means "reject").
    fn oracle_tail_has_nonzero(data: &[u8]) -> bool {
        data.iter().any(|byte| *byte != 0)
    }

    // Oracle 2: the whole-page check of `account_is_zeroed_program_page`,
    // verbatim.
    fn oracle_all_zero(data: &[u8]) -> bool {
        data.iter().all(|byte| *byte == 0)
    }

    // Oracle 3: `validate_root_page_bytes` before the change, verbatim.
    fn oracle_validate_root_page_bytes(
        data: &[u8],
        expected_pool: &Pubkey,
        expected_page_number: u64,
    ) -> Result<RootPageHeaderV1, ProgramError> {
        if data.len() != POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES
            || data[..4] != POOL_V1_ROOT_HISTORY_PAGE_MAGIC
            || data[4] != POOL_V1_ROOT_HISTORY_PAGE_VERSION
            || data[5] != POOL_V1_ROOT_HISTORY_CAPACITY_LOG2
            || data[6] != POOL_V1_DIGEST_ENCODING_VERSION
            || data[7] != 0
            || data[58..64] != [0u8; 6]
        {
            return Err(PoolV1ProgramError::InvalidAccountType.into());
        }
        let pool = Pubkey::new_from_array(
            data[PAGE_POOL_OFFSET..PAGE_NUMBER_OFFSET]
                .try_into()
                .unwrap(),
        );
        let page_number = u64::from_le_bytes(
            data[PAGE_NUMBER_OFFSET..PAGE_FIRST_SEQUENCE_OFFSET]
                .try_into()
                .unwrap(),
        );
        let first_sequence = u64::from_le_bytes(
            data[PAGE_FIRST_SEQUENCE_OFFSET..PAGE_FILLED_OFFSET]
                .try_into()
                .unwrap(),
        );
        let filled = u16::from_le_bytes(data[PAGE_FILLED_OFFSET..58].try_into().unwrap());
        let expected_first = page_number
            .checked_mul(POOL_V1_ROOT_HISTORY_CAPACITY as u64)
            .ok_or(PoolV1ProgramError::ArithmeticOverflow)?;
        if pool != *expected_pool
            || page_number != expected_page_number
            || first_sequence != expected_first
            || usize::from(filled) > POOL_V1_ROOT_HISTORY_CAPACITY
        {
            return Err(PoolV1ProgramError::StateHistoryMismatch.into());
        }
        for slot in 0..usize::from(filled) {
            let start = PAGE_ROOTS_OFFSET + slot * 32;
            decode_digest_canonical(data[start..start + 32].try_into().unwrap())
                .map_err(|_| ProgramError::InvalidAccountData)?;
        }
        let unused_start = PAGE_ROOTS_OFFSET + usize::from(filled) * 32;
        if data[unused_start..].iter().any(|byte| *byte != 0) {
            return Err(ProgramError::InvalidAccountData);
        }
        Ok(RootPageHeaderV1 {
            pool,
            page_number,
            first_sequence,
            filled,
        })
    }

    // Oracle 4: `validate_new_page_account` before the change, verbatim.
    fn oracle_validate_new_page_account(
        program_id: &Pubkey,
        pool: &Pubkey,
        page_number: u64,
        account: &AccountInfo,
    ) -> Result<(), ProgramError> {
        require_program_account(account, program_id, true)?;
        require_root_page_address(program_id, pool, page_number, account)?;
        let data = account.try_borrow_data()?;
        if data.len() != POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES || data.iter().any(|byte| *byte != 0) {
            return Err(ProgramError::InvalidAccountData);
        }
        Ok(())
    }

    fn agree(data: &[u8]) -> bool {
        let new = page_bytes_are_zero(data);
        assert_eq!(new, !oracle_tail_has_nonzero(data), "tail oracle, len {}", data.len());
        assert_eq!(new, oracle_all_zero(data), "page oracle, len {}", data.len());
        new
    }

    // Region lengths the Pool checks: the unused tail for every fill
    // (8,192 down to 0 bytes in steps of 32) and the whole page (8,256).
    fn pool_lengths() -> Vec<usize> {
        let mut lengths: Vec<usize> = (0..=POOL_V1_ROOT_HISTORY_CAPACITY)
            .map(|filled| PAGE - PAGE_ROOTS_OFFSET - 32 * filled)
            .collect();
        lengths.push(PAGE);
        lengths
    }

    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0
        }
        fn below(&mut self, n: usize) -> usize {
            (self.next() % n as u64) as usize
        }
        fn nonzero_byte(&mut self) -> u8 {
            1 + (self.next() % 255) as u8
        }
    }

    #[test]
    fn empty_region_is_zero() {
        assert!(agree(&[]));
    }

    #[test]
    fn zero_regions_of_every_length_up_to_a_page() {
        let zeros = vec![0u8; PAGE];
        for len in 0..=PAGE {
            assert!(agree(&zeros[..len]));
        }
        for len in pool_lengths() {
            assert!(agree(&zeros[..len]));
            // The same lengths at an odd offset inside a larger buffer.
            let wide = vec![0u8; len + 3];
            assert!(agree(&wide[3..]));
        }
    }

    #[test]
    fn one_nonzero_byte_at_every_position_of_a_page() {
        let mut data = vec![0u8; PAGE];
        for position in 0..PAGE {
            for value in [1u8, 0x80, 0xff] {
                data[position] = value;
                assert!(!agree(&data), "position {position} value {value}");
                data[position] = 0;
            }
        }
        assert!(agree(&data));
    }

    #[test]
    fn one_nonzero_byte_at_every_position_of_representative_tails() {
        for filled in [0usize, 1, 2, 3, 4, 31, 127, 128, 200, 254, 255] {
            let len = PAGE - PAGE_ROOTS_OFFSET - 32 * filled;
            let mut data = vec![0u8; len];
            for position in 0..len {
                data[position] = 1 + (position % 255) as u8;
                assert!(!agree(&data), "filled {filled} position {position}");
                data[position] = 0;
            }
        }
    }

    #[test]
    fn nonzero_first_and_last_byte_at_every_length() {
        for len in 1..=PAGE {
            let mut data = vec![0u8; len];
            data[0] = 7;
            assert!(!agree(&data), "first, len {len}");
            data[0] = 0;
            data[len - 1] = 0xff;
            assert!(!agree(&data), "last, len {len}");
        }
    }

    #[test]
    fn uniform_nonzero_regions_are_rejected() {
        // Every byte equal to its successor but the first byte non-zero: the
        // case that the first-byte test alone excludes.
        for len in [1usize, 2, 7, 8, 9, 32, 4128, 8192, PAGE] {
            for value in [1u8, 0x55, 0xff] {
                assert!(!agree(&vec![value; len]), "len {len} value {value}");
            }
        }
    }

    #[test]
    fn pseudo_random_regions() {
        let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
        let mut nonzero = 0usize;
        let mut buffer = vec![0u8; PAGE];
        for round in 0..100_000usize {
            let len = match round % 4 {
                0 => rng.below(PAGE + 1),
                1 => rng.below(65),
                2 => {
                    let lengths = pool_lengths();
                    lengths[rng.below(lengths.len())]
                }
                _ => PAGE,
            };
            buffer[..len].fill(0);
            match round % 5 {
                // all zero
                0 => {}
                // one to three non-zero bytes anywhere
                1 | 2 => {
                    if len > 0 {
                        for _ in 0..1 + rng.below(3) {
                            let position = rng.below(len);
                            buffer[position] = rng.nonzero_byte();
                        }
                    }
                }
                // a non-zero byte near either end
                3 => {
                    if len > 0 {
                        let offset = rng.below(len.min(9));
                        let position = if rng.next() & 1 == 0 { offset } else { len - 1 - offset };
                        buffer[position] = rng.nonzero_byte();
                    }
                }
                // dense random bytes
                _ => {
                    for byte in buffer[..len].iter_mut() {
                        *byte = rng.next() as u8;
                    }
                }
            }
            if !agree(&buffer[..len]) {
                nonzero += 1;
            }
        }
        // Both classes are well represented.
        assert!(nonzero > 40_000 && nonzero < 90_000, "non-zero regions {nonzero}");
    }

    fn root(seed: u32) -> aspis_statement::poseidon2::Digest {
        core::array::from_fn(|index| M31(seed + index as u32))
    }

    #[test]
    fn validate_root_page_bytes_agrees_with_the_old_decoder_on_planted_tails() {
        let pool = Pubkey::new_unique();
        for filled in [0usize, 1, 2, 3, 4, 100, 254, 255, 256] {
            let roots: Vec<_> = (0..filled).map(|index| root(1_000 + 9 * index as u32)).collect();
            let mut data = vec![0u8; PAGE];
            initialize_root_history_page_bytes_v1(&mut data, pool.to_bytes(), 0, &roots).unwrap();
            let clean = validate_root_page_bytes(&data, &pool, 0);
            assert_eq!(clean, oracle_validate_root_page_bytes(&data, &pool, 0));
            assert_eq!(clean.unwrap().filled as usize, filled);
            for position in PAGE_ROOTS_OFFSET + 32 * filled..PAGE {
                data[position] = 0x5a;
                let new = validate_root_page_bytes(&data, &pool, 0);
                assert_eq!(new, oracle_validate_root_page_bytes(&data, &pool, 0));
                assert_eq!(new, Err(ProgramError::InvalidAccountData), "filled {filled} position {position}");
                data[position] = 0;
            }
        }
    }

    #[test]
    fn validate_new_page_account_agrees_with_the_old_check() {
        let program_id = Pubkey::new_unique();
        let pool = Pubkey::new_unique();
        let page_number = 3;
        let key = pool_v1_root_page_address(&program_id, &pool, page_number).0;
        let mut positions: Vec<Option<usize>> = vec![None, Some(0), Some(1), Some(PAGE / 2), Some(PAGE - 2), Some(PAGE - 1)];
        let mut rng = Rng(77);
        for _ in 0..64 {
            positions.push(Some(rng.below(PAGE)));
        }
        for len in [PAGE, PAGE - 1, PAGE + 1, 0] {
            for position in &positions {
                let mut data = vec![0u8; len];
                if let Some(position) = position {
                    if *position < len {
                        data[*position] = 1;
                    }
                }
                let mut lamports = 1u64;
                let info = AccountInfo::new(&key, false, true, &mut lamports, &mut data, &program_id, false, Epoch::default());
                let new = validate_new_page_account(&program_id, &pool, page_number, &info);
                let old = oracle_validate_new_page_account(&program_id, &pool, page_number, &info);
                assert_eq!(new, old, "len {len} position {position:?}");
                assert_eq!(new.is_ok(), len == PAGE && (position.is_none() || position.unwrap() >= len));
            }
        }
    }
}
