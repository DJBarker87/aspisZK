from pathlib import Path
import difflib, hashlib
source=Path('crates/aspis-r1-cost-probe/src/r1_wire.rs')
old=source.read_text()
assert hashlib.sha256(source.read_bytes()).hexdigest()=='ed6e426c460c97248d124727e8be7985c1ea75f89bd0f5baef0570ec44ec4b03'
helper='''
fn parse_records_into<'a>(bytes: &'a [u8], records: &mut [&'a [u8]; 27]) -> Result<(), Error> {
    let mut offset = 32;
    let mut row = 0u8;
    while row < 27 {
        let length = 5 + row_shape(row).unwrap().1;
        let framed = bytes
            .get(offset..offset + length)
            .ok_or(Error::Length { row })?;
        parse_record(row, framed)?;
        records[row as usize] = framed;
        offset += length;
        row += 1;
    }
    if offset != bytes.len() {
        return Err(Error::TrailingBytes);
    }
    Ok(())
}

'''
start=old.index('    pub fn parse(bytes:')
end=old.index('    pub fn record(&self, row:',start)
original_parser=old[start:end]
block_start=original_parser.index('        let mut offset = 32;')
block_end=original_parser.index('        Ok(Self { c1_root, records })')
new_parser=original_parser[:block_start]+'        parse_records_into(bytes, &mut records)?;\n'+original_parser[block_end:]
new=old.replace("impl<'a> Prefix<'a> {",helper+"impl<'a> Prefix<'a> {",1).replace(original_parser,new_parser,1)
reference=original_parser.replace("    pub fn parse(bytes: &'a [u8]) -> Result<Self, Error>","    fn parse_reference<'a>(bytes: &'a [u8]) -> Result<Prefix<'a>, Error>",1).replace('Ok(Self { c1_root, records })','Ok(Prefix { c1_root, records })',1)
tests='''
#[cfg(test)]
mod prefix_parser_tests {
    use super::*;
    use aspis_core::field::P;

    // Freeze the complete pre-refactor parser, including its error ordering.
REFERENCE
    fn fixture() -> (Vec<u8>, [usize; 28]) {
        let mut bytes = alloc::vec![255u8; 32];
        let mut offsets = [0usize; 28];
        offsets[0] = bytes.len();
        for row in 0..27u8 {
            let (tag, size) = row_shape(row).unwrap();
            bytes.push(tag);
            bytes.extend_from_slice(&(size as u32).to_le_bytes());
            let payload_start = bytes.len();
            bytes.resize(payload_start + size, 0);
            if row == 2 {
                bytes[payload_start..].fill(255);
            } else if row >= 14 {
                for value in bytes[payload_start..].chunks_exact_mut(32) {
                    for limb in 0..4 {
                        value[4 * limb..4 * limb + 4].copy_from_slice(&(P - 1).to_le_bytes());
                    }
                }
            }
            offsets[row as usize + 1] = bytes.len();
        }
        (bytes, offsets)
    }

    fn check_error(bytes: &[u8], expected: Error) {
        assert_eq!(parse_reference(bytes).err(), Some(expected));
        assert_eq!(Prefix::parse(bytes).err(), Some(expected));
    }

    #[test]
    fn prefix_into_preserves_slices_and_all_truncations() {
        let (bytes, offsets) = fixture();
        let actual = Prefix::parse(&bytes).unwrap();
        let expected = parse_reference(&bytes).unwrap();
        assert_eq!(actual.c1_root, expected.c1_root);
        assert_eq!(actual.c1_root.as_ptr(), bytes.as_ptr());
        // The helper overwrites every entry; no empty-slice seed assumption.
        let mut scratch = [&bytes[..1]; 27];
        parse_records_into(&bytes, &mut scratch).unwrap();
        for row in 0..27u8 {
            let start = offsets[row as usize];
            let end = offsets[row as usize + 1];
            let frame = actual.record(row).unwrap();
            assert_eq!(frame, expected.record(row).unwrap());
            assert_eq!(frame, &bytes[start..end]);
            assert_eq!(frame.as_ptr(), bytes[start..end].as_ptr());
            assert_eq!(scratch[row as usize].as_ptr(), frame.as_ptr());
            assert_eq!(scratch[row as usize].len(), frame.len());
            let payload = actual.payload(row).unwrap();
            assert_eq!(payload, expected.payload(row).unwrap());
            assert_eq!(payload.as_ptr(), bytes[start + 5..end].as_ptr());
            let token = actual.validated_record(row).unwrap();
            assert_eq!(token.row(), row);
            assert_eq!(token.framed().as_ptr(), frame.as_ptr());
            assert_eq!(token.payload(), payload);
        }
        for row in 27..=u8::MAX {
            assert_eq!(actual.record(row), Err(Error::InvalidRow));
            assert_eq!(actual.payload(row), Err(Error::InvalidRow));
            assert_eq!(actual.validated_record(row).err(), Some(Error::InvalidRow));
        }
        for length in 0..bytes.len() {
            let row = (0..27).find(|row| length < offsets[row + 1]).unwrap() as u8;
            check_error(&bytes[..length], Error::Length { row });
        }
        for suffix in [alloc::vec![0], alloc::vec![255; 32]] {
            let mut extra = bytes.clone();
            extra.extend_from_slice(&suffix);
            check_error(&extra, Error::TrailingBytes);
        }
    }

    #[test]
    fn prefix_into_preserves_framing_and_cross_row_error_order() {
        let (bytes, offsets) = fixture();
        for row in 0..27u8 {
            let start = offsets[row as usize];
            let mut bad_tag = bytes.clone();
            bad_tag[start] ^= 255;
            bad_tag[start + 1..start + 5].fill(255);
            check_error(&bad_tag, Error::Tag { row });
            // An early invalid tag wins over both later truncation and suffix.
            bad_tag.push(0);
            check_error(&bad_tag, Error::Tag { row });
            check_error(&bad_tag[..offsets[row as usize + 1]], Error::Tag { row });
            let mut bad_length = bytes.clone();
            bad_length[start + 1..start + 5].fill(255);
            check_error(&bad_length, Error::Length { row });
            if row < 26 {
                bad_length[offsets[row as usize + 1]] ^= 255;
                check_error(&bad_length, Error::Length { row });
            }
        }
    }

    #[test]
    fn prefix_into_preserves_first_field_failure() {
        let (bytes, offsets) = fixture();
        for row in 14..27u8 {
            let payload_start = offsets[row as usize] + 5;
            let values = (offsets[row as usize + 1] - payload_start) / 32;
            for value in [0, values - 1] {
                for limb in 0..8 {
                    for bad in [P, u32::MAX] {
                        let mut malformed = bytes.clone();
                        let offset = payload_start + value * 32 + limb * 4;
                        malformed[offset..offset + 4].copy_from_slice(&bad.to_le_bytes());
                        check_error(&malformed, Error::NonCanonical { row, value });
                    }
                }
                for limb in 4..8 {
                    let mut high_nonzero = bytes.clone();
                    let offset = payload_start + value * 32 + limb * 4;
                    high_nonzero[offset..offset + 4].copy_from_slice(&1u32.to_le_bytes());
                    // An earlier field failure wins over a trailing suffix.
                    high_nonzero.push(255);
                    check_error(&high_nonzero, Error::NonCanonical { row, value });
                }
            }
            let mut two_errors = bytes.clone();
            two_errors[payload_start + 16..payload_start + 20]
                .copy_from_slice(&1u32.to_le_bytes());
            if values > 1 {
                two_errors[payload_start + 32..payload_start + 36]
                    .copy_from_slice(&P.to_le_bytes());
            }
            if row < 26 {
                two_errors[offsets[row as usize + 1]] ^= 255;
            }
            check_error(&two_errors, Error::NonCanonical { row, value: 0 });
        }
    }
}
'''.replace('REFERENCE',reference.rstrip())
new+=tests
patch=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+str(source),tofile='b/'+str(source)))
out=Path('docs/research/100bit-spend-path-20261013/design/J1-R18-PREFIX-IMPLEMENTATION-DRAFT-20261016.patch');out.write_text(patch)
print(out, 'bytes', len(patch.encode()), 'sha256',hashlib.sha256(patch.encode()).hexdigest())
assert source.read_text()==old
