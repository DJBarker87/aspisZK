//! Default-off terminal PDA bump certificate wire.
//!
//! This is proof-account plumbing, not a proof or statement format.  A
//! verifier-owned certificate is populated before the terminal transaction
//! only after every address below has been derived with Solana's canonical
//! bump search.  The hot path uses the recorded bumps with one-attempt
//! `create_program_address` and compares every resulting address.

use crate::decode_digest_canonical;

pub const POOL_V1_TERMINAL_PDA_CERTIFICATE_MAGIC: [u8; 4] = *b"APD8";
pub const POOL_V1_TERMINAL_PDA_CERTIFICATE_VERSION: u8 = 1;
pub const POOL_V1_TERMINAL_PDA_CERTIFICATE_FLAG_ROLLOVER: u8 = 1;
pub const POOL_V1_TERMINAL_PDA_CERTIFICATE_FLAG_WITHDRAWAL: u8 = 2;
pub const POOL_V1_TERMINAL_PDA_CERTIFICATE_FLAGS: u8 =
    POOL_V1_TERMINAL_PDA_CERTIFICATE_FLAG_ROLLOVER
        | POOL_V1_TERMINAL_PDA_CERTIFICATE_FLAG_WITHDRAWAL;
pub const POOL_V1_TERMINAL_PDA_CERTIFICATE_ACCOUNT_BYTES: usize = 704;

const PROOF_OFFSET: usize = 8;
const POOL_PROGRAM_OFFSET: usize = 40;
const MASTER_OFFSET: usize = 72;
const MINT_OFFSET: usize = 104;
const CHECKPOINT_OFFSET: usize = 136;
const CHECKPOINT_SEQUENCE_OFFSET: usize = 168;
const LANE_OFFSET: usize = 176;
const LANE_ID_OFFSET: usize = 208;
const CURRENT_PAGE_OFFSET: usize = 216;
const CURRENT_PAGE_NUMBER_OFFSET: usize = 248;
const NEXT_PAGE_OFFSET: usize = 256;
const NEXT_PAGE_NUMBER_OFFSET: usize = 288;
const MARKER_OFFSET: usize = 296;
const NULLIFIER_OFFSET: usize = 328;
const REGISTRY_PROGRAM_OFFSET: usize = 360;
const REGISTRY_OFFSET: usize = 392;
const REGISTRY_PROGRAMDATA_OFFSET: usize = 424;
const ENTRY_OFFSET: usize = 456;
const VERIFIER_PROGRAM_OFFSET: usize = 488;
const VERIFIER_PROGRAMDATA_OFFSET: usize = 520;
const VAULT_AUTHORITY_OFFSET: usize = 552;
const VAULT_TOKEN_OFFSET: usize = 584;
const PROFILE_OFFSET: usize = 616;
const RELEASE_OFFSET: usize = 648;
const BUMPS_OFFSET: usize = 680;
const RESERVED_OFFSET: usize = 692;

pub const POOL_V1_TERMINAL_PDA_BUMP_MASTER: usize = 0;
pub const POOL_V1_TERMINAL_PDA_BUMP_CHECKPOINT: usize = 1;
pub const POOL_V1_TERMINAL_PDA_BUMP_LANE: usize = 2;
pub const POOL_V1_TERMINAL_PDA_BUMP_CURRENT_PAGE: usize = 3;
pub const POOL_V1_TERMINAL_PDA_BUMP_NEXT_PAGE: usize = 4;
pub const POOL_V1_TERMINAL_PDA_BUMP_MARKER: usize = 5;
pub const POOL_V1_TERMINAL_PDA_BUMP_REGISTRY: usize = 6;
pub const POOL_V1_TERMINAL_PDA_BUMP_REGISTRY_PROGRAMDATA: usize = 7;
pub const POOL_V1_TERMINAL_PDA_BUMP_ENTRY: usize = 8;
pub const POOL_V1_TERMINAL_PDA_BUMP_VERIFIER_PROGRAMDATA: usize = 9;
pub const POOL_V1_TERMINAL_PDA_BUMP_VAULT_AUTHORITY: usize = 10;
pub const POOL_V1_TERMINAL_PDA_BUMP_VAULT_TOKEN: usize = 11;
pub const POOL_V1_TERMINAL_PDA_BUMP_COUNT: usize = 12;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1TerminalPdaCertificateErrorV1 {
    WrongLength,
    WrongMagic,
    WrongVersion,
    UnsupportedFlags,
    NonZeroReserved,
    ZeroRequiredIdentity,
    InvalidLane,
    NonCanonicalNullifier,
    InvalidOptionalIdentity,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1TerminalPdaCertificateV1 {
    pub flags: u8,
    pub proof_account: [u8; 32],
    pub pool_program: [u8; 32],
    pub master: [u8; 32],
    pub asset_mint: [u8; 32],
    pub checkpoint: [u8; 32],
    pub checkpoint_sequence: u64,
    pub selected_lane: [u8; 32],
    pub lane_id: u8,
    pub current_history_page: [u8; 32],
    pub current_page_number: u64,
    pub next_history_page: [u8; 32],
    pub next_page_number: u64,
    pub nullifier_marker: [u8; 32],
    pub canonical_nullifier: [u8; 32],
    pub registry_program: [u8; 32],
    pub registry: [u8; 32],
    pub registry_programdata: [u8; 32],
    pub registry_entry: [u8; 32],
    pub verifier_program: [u8; 32],
    pub verifier_programdata: [u8; 32],
    pub vault_authority: [u8; 32],
    pub vault_token: [u8; 32],
    pub profile_binding: [u8; 32],
    pub release_binding: [u8; 32],
    pub bumps: [u8; POOL_V1_TERMINAL_PDA_BUMP_COUNT],
}

impl PoolV1TerminalPdaCertificateV1 {
    pub fn rollover(&self) -> bool {
        self.flags & POOL_V1_TERMINAL_PDA_CERTIFICATE_FLAG_ROLLOVER != 0
    }

    pub fn withdrawal(&self) -> bool {
        self.flags & POOL_V1_TERMINAL_PDA_CERTIFICATE_FLAG_WITHDRAWAL != 0
    }

    pub fn validate(&self) -> Result<(), PoolV1TerminalPdaCertificateErrorV1> {
        if self.flags & !POOL_V1_TERMINAL_PDA_CERTIFICATE_FLAGS != 0 {
            return Err(PoolV1TerminalPdaCertificateErrorV1::UnsupportedFlags);
        }
        let required = [
            self.proof_account,
            self.pool_program,
            self.master,
            self.asset_mint,
            self.checkpoint,
            self.selected_lane,
            self.current_history_page,
            self.nullifier_marker,
            self.registry_program,
            self.registry,
            self.registry_programdata,
            self.registry_entry,
            self.verifier_program,
            self.verifier_programdata,
            self.profile_binding,
            self.release_binding,
        ];
        if required.iter().any(|value| *value == [0u8; 32]) {
            return Err(PoolV1TerminalPdaCertificateErrorV1::ZeroRequiredIdentity);
        }
        if usize::from(self.lane_id) >= 8 {
            return Err(PoolV1TerminalPdaCertificateErrorV1::InvalidLane);
        }
        decode_digest_canonical(&self.canonical_nullifier)
            .map_err(|_| PoolV1TerminalPdaCertificateErrorV1::NonCanonicalNullifier)?;
        let next_absent = self.next_history_page == [0u8; 32] && self.next_page_number == 0;
        let vault_absent = self.vault_authority == [0u8; 32] && self.vault_token == [0u8; 32];
        if next_absent == self.rollover() || vault_absent == self.withdrawal() {
            return Err(PoolV1TerminalPdaCertificateErrorV1::InvalidOptionalIdentity);
        }
        for (index, bump) in self.bumps.iter().copied().enumerate() {
            let optional_absent = (index == POOL_V1_TERMINAL_PDA_BUMP_NEXT_PAGE
                && !self.rollover())
                || ((index == POOL_V1_TERMINAL_PDA_BUMP_VAULT_AUTHORITY
                    || index == POOL_V1_TERMINAL_PDA_BUMP_VAULT_TOKEN)
                    && !self.withdrawal());
            // A canonical Solana PDA bump can be any u8, including zero.  A
            // required bump is therefore canonical only after the owning
            // verifier has recomputed the exact `(address, bump)` pair.  The
            // codec constrains only absent optional slots to their unique
            // zero representation.
            if optional_absent && bump != 0 {
                return Err(PoolV1TerminalPdaCertificateErrorV1::InvalidOptionalIdentity);
            }
        }
        Ok(())
    }
}

pub fn encode_pool_v1_terminal_pda_certificate_v1(
    certificate: &PoolV1TerminalPdaCertificateV1,
) -> Result<[u8; POOL_V1_TERMINAL_PDA_CERTIFICATE_ACCOUNT_BYTES], PoolV1TerminalPdaCertificateErrorV1>
{
    certificate.validate()?;
    let mut out = [0u8; POOL_V1_TERMINAL_PDA_CERTIFICATE_ACCOUNT_BYTES];
    out[..4].copy_from_slice(&POOL_V1_TERMINAL_PDA_CERTIFICATE_MAGIC);
    out[4] = POOL_V1_TERMINAL_PDA_CERTIFICATE_VERSION;
    out[5] = certificate.flags;
    macro_rules! put32 {
        ($offset:expr, $field:ident) => {
            out[$offset..$offset + 32].copy_from_slice(&certificate.$field)
        };
    }
    put32!(PROOF_OFFSET, proof_account);
    put32!(POOL_PROGRAM_OFFSET, pool_program);
    put32!(MASTER_OFFSET, master);
    put32!(MINT_OFFSET, asset_mint);
    put32!(CHECKPOINT_OFFSET, checkpoint);
    out[CHECKPOINT_SEQUENCE_OFFSET..CHECKPOINT_SEQUENCE_OFFSET + 8]
        .copy_from_slice(&certificate.checkpoint_sequence.to_le_bytes());
    put32!(LANE_OFFSET, selected_lane);
    out[LANE_ID_OFFSET] = certificate.lane_id;
    put32!(CURRENT_PAGE_OFFSET, current_history_page);
    out[CURRENT_PAGE_NUMBER_OFFSET..CURRENT_PAGE_NUMBER_OFFSET + 8]
        .copy_from_slice(&certificate.current_page_number.to_le_bytes());
    put32!(NEXT_PAGE_OFFSET, next_history_page);
    out[NEXT_PAGE_NUMBER_OFFSET..NEXT_PAGE_NUMBER_OFFSET + 8]
        .copy_from_slice(&certificate.next_page_number.to_le_bytes());
    put32!(MARKER_OFFSET, nullifier_marker);
    put32!(NULLIFIER_OFFSET, canonical_nullifier);
    put32!(REGISTRY_PROGRAM_OFFSET, registry_program);
    put32!(REGISTRY_OFFSET, registry);
    put32!(REGISTRY_PROGRAMDATA_OFFSET, registry_programdata);
    put32!(ENTRY_OFFSET, registry_entry);
    put32!(VERIFIER_PROGRAM_OFFSET, verifier_program);
    put32!(VERIFIER_PROGRAMDATA_OFFSET, verifier_programdata);
    put32!(VAULT_AUTHORITY_OFFSET, vault_authority);
    put32!(VAULT_TOKEN_OFFSET, vault_token);
    put32!(PROFILE_OFFSET, profile_binding);
    put32!(RELEASE_OFFSET, release_binding);
    out[BUMPS_OFFSET..RESERVED_OFFSET].copy_from_slice(&certificate.bumps);
    Ok(out)
}

pub fn decode_pool_v1_terminal_pda_certificate_v1(
    bytes: &[u8],
) -> Result<PoolV1TerminalPdaCertificateV1, PoolV1TerminalPdaCertificateErrorV1> {
    if bytes.len() != POOL_V1_TERMINAL_PDA_CERTIFICATE_ACCOUNT_BYTES {
        return Err(PoolV1TerminalPdaCertificateErrorV1::WrongLength);
    }
    if bytes[..4] != POOL_V1_TERMINAL_PDA_CERTIFICATE_MAGIC {
        return Err(PoolV1TerminalPdaCertificateErrorV1::WrongMagic);
    }
    if bytes[4] != POOL_V1_TERMINAL_PDA_CERTIFICATE_VERSION {
        return Err(PoolV1TerminalPdaCertificateErrorV1::WrongVersion);
    }
    if bytes[6..8] != [0u8; 2]
        || bytes[LANE_ID_OFFSET + 1..CURRENT_PAGE_OFFSET] != [0u8; 7]
        || bytes[RESERVED_OFFSET..].iter().any(|byte| *byte != 0)
    {
        return Err(PoolV1TerminalPdaCertificateErrorV1::NonZeroReserved);
    }
    let get32 = |offset: usize| -> [u8; 32] { bytes[offset..offset + 32].try_into().unwrap() };
    let certificate = PoolV1TerminalPdaCertificateV1 {
        flags: bytes[5],
        proof_account: get32(PROOF_OFFSET),
        pool_program: get32(POOL_PROGRAM_OFFSET),
        master: get32(MASTER_OFFSET),
        asset_mint: get32(MINT_OFFSET),
        checkpoint: get32(CHECKPOINT_OFFSET),
        checkpoint_sequence: u64::from_le_bytes(
            bytes[CHECKPOINT_SEQUENCE_OFFSET..CHECKPOINT_SEQUENCE_OFFSET + 8]
                .try_into()
                .unwrap(),
        ),
        selected_lane: get32(LANE_OFFSET),
        lane_id: bytes[LANE_ID_OFFSET],
        current_history_page: get32(CURRENT_PAGE_OFFSET),
        current_page_number: u64::from_le_bytes(
            bytes[CURRENT_PAGE_NUMBER_OFFSET..CURRENT_PAGE_NUMBER_OFFSET + 8]
                .try_into()
                .unwrap(),
        ),
        next_history_page: get32(NEXT_PAGE_OFFSET),
        next_page_number: u64::from_le_bytes(
            bytes[NEXT_PAGE_NUMBER_OFFSET..NEXT_PAGE_NUMBER_OFFSET + 8]
                .try_into()
                .unwrap(),
        ),
        nullifier_marker: get32(MARKER_OFFSET),
        canonical_nullifier: get32(NULLIFIER_OFFSET),
        registry_program: get32(REGISTRY_PROGRAM_OFFSET),
        registry: get32(REGISTRY_OFFSET),
        registry_programdata: get32(REGISTRY_PROGRAMDATA_OFFSET),
        registry_entry: get32(ENTRY_OFFSET),
        verifier_program: get32(VERIFIER_PROGRAM_OFFSET),
        verifier_programdata: get32(VERIFIER_PROGRAMDATA_OFFSET),
        vault_authority: get32(VAULT_AUTHORITY_OFFSET),
        vault_token: get32(VAULT_TOKEN_OFFSET),
        profile_binding: get32(PROFILE_OFFSET),
        release_binding: get32(RELEASE_OFFSET),
        bumps: bytes[BUMPS_OFFSET..RESERVED_OFFSET].try_into().unwrap(),
    };
    certificate.validate()?;
    Ok(certificate)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn certificate() -> PoolV1TerminalPdaCertificateV1 {
        PoolV1TerminalPdaCertificateV1 {
            flags: POOL_V1_TERMINAL_PDA_CERTIFICATE_FLAG_ROLLOVER
                | POOL_V1_TERMINAL_PDA_CERTIFICATE_FLAG_WITHDRAWAL,
            proof_account: [1; 32],
            pool_program: [2; 32],
            master: [3; 32],
            asset_mint: [4; 32],
            checkpoint: [5; 32],
            checkpoint_sequence: 6,
            selected_lane: [7; 32],
            lane_id: 3,
            current_history_page: [8; 32],
            current_page_number: 9,
            next_history_page: [10; 32],
            next_page_number: 10,
            nullifier_marker: [11; 32],
            canonical_nullifier: [12; 32],
            registry_program: [13; 32],
            registry: [14; 32],
            registry_programdata: [15; 32],
            registry_entry: [16; 32],
            verifier_program: [17; 32],
            verifier_programdata: [18; 32],
            vault_authority: [19; 32],
            vault_token: [20; 32],
            profile_binding: [21; 32],
            release_binding: [22; 32],
            bumps: [255, 254, 253, 252, 251, 250, 249, 248, 247, 246, 245, 244],
        }
    }

    #[test]
    fn roundtrip_and_corruption_fail_closed() {
        let value = certificate();
        let encoded = encode_pool_v1_terminal_pda_certificate_v1(&value).unwrap();
        assert_eq!(
            encoded.len(),
            POOL_V1_TERMINAL_PDA_CERTIFICATE_ACCOUNT_BYTES
        );
        assert_eq!(
            decode_pool_v1_terminal_pda_certificate_v1(&encoded),
            Ok(value)
        );

        let mut changed = encoded;
        changed[RESERVED_OFFSET] = 1;
        assert_eq!(
            decode_pool_v1_terminal_pda_certificate_v1(&changed),
            Err(PoolV1TerminalPdaCertificateErrorV1::NonZeroReserved)
        );
        let mut zero_bump = value;
        zero_bump.bumps[POOL_V1_TERMINAL_PDA_BUMP_MASTER] = 0;
        assert!(encode_pool_v1_terminal_pda_certificate_v1(&zero_bump).is_ok());
    }

    #[test]
    fn optional_fields_are_exact() {
        let mut value = certificate();
        value.flags = 0;
        value.next_history_page = [0; 32];
        value.next_page_number = 0;
        value.vault_authority = [0; 32];
        value.vault_token = [0; 32];
        value.bumps[POOL_V1_TERMINAL_PDA_BUMP_NEXT_PAGE] = 0;
        value.bumps[POOL_V1_TERMINAL_PDA_BUMP_VAULT_AUTHORITY] = 0;
        value.bumps[POOL_V1_TERMINAL_PDA_BUMP_VAULT_TOKEN] = 0;
        assert!(encode_pool_v1_terminal_pda_certificate_v1(&value).is_ok());
        value.next_history_page = [1; 32];
        assert_eq!(
            value.validate(),
            Err(PoolV1TerminalPdaCertificateErrorV1::InvalidOptionalIdentity)
        );
    }
}
