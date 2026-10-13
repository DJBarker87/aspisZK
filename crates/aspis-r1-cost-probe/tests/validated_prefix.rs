use aspis_r1_cost_probe::r1_wire::{self, Error, Prefix, SemanticTranscript};

fn test_hash(parts: &[&[u8]]) -> [u8; 32] {
    let mut out = [0u8; 32];
    for (part_index, part) in parts.iter().enumerate() {
        for (i, byte) in part.iter().enumerate() {
            let slot = (i + part_index * 7) % 32;
            out[slot] = out[slot]
                .wrapping_mul(31)
                .wrapping_add(*byte)
                .wrapping_add(i as u8);
        }
    }
    out
}

fn valid_prefix() -> Vec<u8> {
    let mut bytes = vec![0u8; 32];
    for row in 0..27 {
        let size = r1_wire::row_shape(row).unwrap().1;
        bytes.extend_from_slice(&r1_wire::record(row, &vec![0; size]).unwrap());
    }
    bytes
}

fn row_offset(row: u8) -> usize {
    32 + (0..row)
        .map(|r| 5 + r1_wire::row_shape(r).unwrap().1)
        .sum::<usize>()
}

#[test]
fn prefix_and_public_transcript_reject_bad_framing_and_field_encodings() {
    let valid = valid_prefix();

    let mut bad_tag = valid.clone();
    bad_tag[row_offset(0)] ^= 1;
    assert!(matches!(
        Prefix::parse(&bad_tag),
        Err(Error::Tag { row: 0 })
    ));
    let mut transcript = SemanticTranscript::new(test_hash, b"public", &[0; 32]).unwrap();
    assert!(matches!(
        transcript.semantic(0, &bad_tag[32..37]),
        Err(Error::Tag { row: 0 })
    ));
    assert_eq!(transcript.next_row(), 0);

    let mut noncanonical = valid.clone();
    let field = row_offset(14) + 5;
    noncanonical[field..field + 4].copy_from_slice(&aspis_core::field::P.to_le_bytes());
    assert!(matches!(
        Prefix::parse(&noncanonical),
        Err(Error::NonCanonical { row: 14, value: 0 })
    ));
    let mut high_component = valid.clone();
    high_component[field + 16] = 1;
    assert!(matches!(
        Prefix::parse(&high_component),
        Err(Error::NonCanonical { row: 14, value: 0 })
    ));

    for malformed in [&noncanonical, &high_component] {
        let mut transcript = SemanticTranscript::new(test_hash, b"public", &[0; 32]).unwrap();
        for row in 0..14 {
            transcript
                .semantic(row, &valid[row_offset(row)..row_offset(row) + 5 + r1_wire::row_shape(row).unwrap().1])
                .unwrap();
        }
        let framed = &malformed[field - 5..field - 5 + 5 + 32];
        assert!(matches!(
            transcript.semantic(14, framed),
            Err(Error::NonCanonical { row: 14, value: 0 })
        ));
        assert_eq!(transcript.next_row(), 14);
    }

    // Raw transcript entrypoints continue validating arbitrary circle records.
    let mut malformed_circle = valid.clone();
    let circle_field = row_offset(25) + 5;
    malformed_circle[circle_field + 16] = 1;
    assert!(matches!(
        Prefix::parse(&malformed_circle),
        Err(Error::NonCanonical { row: 25, value: 0 })
    ));
    let mut transcript = SemanticTranscript::new(test_hash, b"public", &[0; 32]).unwrap();
    for row in 0..25 {
        let start = row_offset(row);
        let size = r1_wire::row_shape(row).unwrap().1;
        transcript
            .semantic(row, &valid[start..start + 5 + size])
            .unwrap();
    }
    let circle_record = &malformed_circle
        [circle_field - 5..circle_field - 5 + 5 + r1_wire::row_shape(25).unwrap().1];
    assert!(matches!(
        transcript.challenge_reference_circle_point(25, circle_record),
        Err(Error::NonCanonical { row: 25, value: 0 })
    ));
    assert_eq!(transcript.next_row(), 25);
}
