//! Shared pair-forest deposit wire helpers; no standalone ASDI entrypoint.

use aspis_core::field::P;
use aspis_statement::{
    decode_digest_canonical, encode_digest_canonical,
    pool_v1::POOL_V1_ENCRYPTED_NOTE_PAYLOAD_MAX_BYTES,
    VALUE_LIMIT,
};

use crate::deposit::DepositRequestV1;

pub const POOL_V1_DEPOSIT_INSTRUCTION_MAGIC: [u8; 4] = *b"ASDI";
pub const POOL_V1_DEPOSIT_INSTRUCTION_VERSION: u8 = 1;
pub const POOL_V1_DEPOSIT_INSTRUCTION_HEADER_BYTES: usize = 80;
pub const POOL_V1_DEPOSIT_INSTRUCTION_MAX_BYTES: usize =
    match POOL_V1_DEPOSIT_INSTRUCTION_HEADER_BYTES
        .checked_add(POOL_V1_ENCRYPTED_NOTE_PAYLOAD_MAX_BYTES)
    {
        Some(length) => length,
        None => panic!("Pool V1 deposit instruction size overflow"),
    };

const INSTRUCTION_OWNER_KEY_OFFSET: usize = 8;
const INSTRUCTION_AMOUNT_OFFSET: usize = 40;
const INSTRUCTION_SALT_OFFSET: usize = 48;
const INSTRUCTION_PAYLOAD_OFFSET: usize = POOL_V1_DEPOSIT_INSTRUCTION_HEADER_BYTES;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DepositInstructionFormatErrorV1 {
    WrongLength,
    WrongMagic,
    WrongVersion,
    NonZeroReserved,
    InvalidAmount,
    InvalidPayloadLength,
    NonCanonicalDigest,
}

/// Fixed-capacity canonical instruction image. Only [`Self::as_bytes`] is part
/// of the wire; unused capacity is never serialized.
pub struct DepositInstructionDataV1 {
    bytes: [u8; POOL_V1_DEPOSIT_INSTRUCTION_MAX_BYTES],
    length: usize,
}

impl DepositInstructionDataV1 {
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes[..self.length]
    }
}

fn digest_is_canonical(digest: &aspis_statement::Digest) -> bool {
    digest.iter().all(|limb| limb.0 < P)
}

/// Encode the only accepted V1 deposit instruction image.
///
/// ```text
/// 0..4    magic ASDI
/// 4       version 1
/// 5       flags 0
/// 6..8    encrypted payload length u16 LE
/// 8..40   owner-key digest (canonical LE M31 limbs)
/// 40..44  amount u32 LE
/// 44..48  zero reserved
/// 48..80  salt digest (canonical LE M31 limbs)
/// 80..N   exact opaque encrypted-note payload
/// ```
pub fn encode_deposit_instruction_v1(
    request: &DepositRequestV1<'_>,
) -> Result<DepositInstructionDataV1, DepositInstructionFormatErrorV1> {
    if request.amount == 0 || request.amount >= VALUE_LIMIT {
        return Err(DepositInstructionFormatErrorV1::InvalidAmount);
    }
    if request.encrypted_note_payload.len() > POOL_V1_ENCRYPTED_NOTE_PAYLOAD_MAX_BYTES {
        return Err(DepositInstructionFormatErrorV1::InvalidPayloadLength);
    }
    if !digest_is_canonical(&request.owner_key) || !digest_is_canonical(&request.salt) {
        return Err(DepositInstructionFormatErrorV1::NonCanonicalDigest);
    }

    let length = INSTRUCTION_PAYLOAD_OFFSET
        .checked_add(request.encrypted_note_payload.len())
        .ok_or(DepositInstructionFormatErrorV1::WrongLength)?;
    let payload_length = u16::try_from(request.encrypted_note_payload.len())
        .map_err(|_| DepositInstructionFormatErrorV1::InvalidPayloadLength)?;
    let mut bytes = [0u8; POOL_V1_DEPOSIT_INSTRUCTION_MAX_BYTES];
    bytes[..4].copy_from_slice(&POOL_V1_DEPOSIT_INSTRUCTION_MAGIC);
    bytes[4] = POOL_V1_DEPOSIT_INSTRUCTION_VERSION;
    bytes[6..8].copy_from_slice(&payload_length.to_le_bytes());
    bytes[INSTRUCTION_OWNER_KEY_OFFSET..INSTRUCTION_AMOUNT_OFFSET]
        .copy_from_slice(&encode_digest_canonical(&request.owner_key));
    bytes[INSTRUCTION_AMOUNT_OFFSET..44].copy_from_slice(&request.amount.to_le_bytes());
    bytes[INSTRUCTION_SALT_OFFSET..INSTRUCTION_PAYLOAD_OFFSET]
        .copy_from_slice(&encode_digest_canonical(&request.salt));
    bytes[INSTRUCTION_PAYLOAD_OFFSET..length].copy_from_slice(request.encrypted_note_payload);
    Ok(DepositInstructionDataV1 { bytes, length })
}

/// Crate-private strict decoder shared by versioned Pool deposit transports.
/// Only the four-byte domain separator varies; the remaining frozen request
/// grammar is byte-identical.
pub(crate) fn decode_deposit_instruction_with_magic_v1(
    bytes: &[u8],
    expected_magic: [u8; 4],
) -> Result<DepositRequestV1<'_>, DepositInstructionFormatErrorV1> {
    if bytes.len() < POOL_V1_DEPOSIT_INSTRUCTION_HEADER_BYTES
        || bytes.len() > POOL_V1_DEPOSIT_INSTRUCTION_MAX_BYTES
    {
        return Err(DepositInstructionFormatErrorV1::WrongLength);
    }
    if bytes[..4] != expected_magic {
        return Err(DepositInstructionFormatErrorV1::WrongMagic);
    }
    if bytes[4] != POOL_V1_DEPOSIT_INSTRUCTION_VERSION {
        return Err(DepositInstructionFormatErrorV1::WrongVersion);
    }
    if bytes[5] != 0 || bytes[44..48] != [0u8; 4] {
        return Err(DepositInstructionFormatErrorV1::NonZeroReserved);
    }

    let declared_payload_length = usize::from(u16::from_le_bytes(
        bytes[6..8]
            .try_into()
            .map_err(|_| DepositInstructionFormatErrorV1::WrongLength)?,
    ));
    if declared_payload_length > POOL_V1_ENCRYPTED_NOTE_PAYLOAD_MAX_BYTES {
        return Err(DepositInstructionFormatErrorV1::InvalidPayloadLength);
    }
    let expected_length = INSTRUCTION_PAYLOAD_OFFSET
        .checked_add(declared_payload_length)
        .ok_or(DepositInstructionFormatErrorV1::WrongLength)?;
    if bytes.len() != expected_length {
        return Err(DepositInstructionFormatErrorV1::WrongLength);
    }

    let owner_key_bytes: &[u8; 32] = bytes[INSTRUCTION_OWNER_KEY_OFFSET..INSTRUCTION_AMOUNT_OFFSET]
        .try_into()
        .map_err(|_| DepositInstructionFormatErrorV1::WrongLength)?;
    let salt_bytes: &[u8; 32] = bytes[INSTRUCTION_SALT_OFFSET..INSTRUCTION_PAYLOAD_OFFSET]
        .try_into()
        .map_err(|_| DepositInstructionFormatErrorV1::WrongLength)?;
    let owner_key = decode_digest_canonical(owner_key_bytes)
        .map_err(|_| DepositInstructionFormatErrorV1::NonCanonicalDigest)?;
    let salt = decode_digest_canonical(salt_bytes)
        .map_err(|_| DepositInstructionFormatErrorV1::NonCanonicalDigest)?;
    let amount = u32::from_le_bytes(
        bytes[INSTRUCTION_AMOUNT_OFFSET..44]
            .try_into()
            .map_err(|_| DepositInstructionFormatErrorV1::WrongLength)?,
    );
    if amount == 0 || amount >= VALUE_LIMIT {
        return Err(DepositInstructionFormatErrorV1::InvalidAmount);
    }

    Ok(DepositRequestV1 {
        owner_key,
        amount,
        salt,
        encrypted_note_payload: &bytes[INSTRUCTION_PAYLOAD_OFFSET..],
    })
}

#[cfg(kani)]
#[path="PCI_DepositNative.rs"]mod PCI_DepositNative;
