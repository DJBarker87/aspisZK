fn decode_fission<'a>(bytes: &'a [u8;592], logical_len: usize, expected_magic: [u8;4]) -> Result<DepositRequestV1<'a>,DepositInstructionFormatErrorV1> {
    if logical_len < POOL_V1_DEPOSIT_INSTRUCTION_HEADER_BYTES
        || logical_len > POOL_V1_DEPOSIT_INSTRUCTION_MAX_BYTES
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
    if logical_len != expected_length {
        return Err(DepositInstructionFormatErrorV1::WrongLength);
    }

    let owner_key_bytes: &[u8; 32] = bytes[INSTRUCTION_OWNER_KEY_OFFSET..INSTRUCTION_AMOUNT_OFFSET]
        .try_into()
        .map_err(|_| DepositInstructionFormatErrorV1::WrongLength)?;
    let salt_bytes: &[u8; 32] = bytes[INSTRUCTION_SALT_OFFSET..INSTRUCTION_PAYLOAD_OFFSET]
        .try_into()
        .map_err(|_| DepositInstructionFormatErrorV1::WrongLength)?;
    #[cfg(PCI_DEPOSIT_ARG_MUTANT)]
    let owner_key_bytes = salt_bytes;
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
        encrypted_note_payload: &bytes[INSTRUCTION_PAYLOAD_OFFSET..logical_len],
    })
}
