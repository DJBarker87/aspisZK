//! UNPROVED COST PROBE. P2 D14-content wire; expanded row 25, isolated from the S4 gate.

use crate::sampler::{circle_sample, qm31_sample, CircleRow};
use alloc::vec::Vec;
use aspis_core::circle::SecureCirclePoint;
use aspis_core::field::{WideExact, QM31};
use aspis_core::Digest32;

#[cfg(not(feature = "private-leaf-salts"))]
pub const DOMAIN: &[u8] = b"aspis:r0:20261009:v1";
#[cfg(feature = "private-leaf-salts")]
pub const DOMAIN: &[u8] = b"UNPROVED:R1:PRIVATE-SALTED:SEMANTIC:P3";
pub const LANES: usize = 29;
pub const POINTS: usize = 3;
pub const CLAIMS: usize = POINTS * LANES;
pub const C1_LANES: [usize; 27] = [
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
    28,
];
pub const C2_LANES: [usize; 2] = [26, 27];
pub type PointClaims = [[WideExact; LANES]; POINTS];

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
    Public, #[cfg(feature = "r1p-check")] ActivePole, // host retry loop only: Lean ¬NoPole, no detail (LOG D73.4.1)
}

/// P1 tag and exact payload length, including the message-free rows.
pub const fn row_shape(row: u8) -> Option<(u8, usize)> {
    match row {
        0 | 1 | 3..=13 => Some((0, 0)),
        2 => Some((1, 32)),
        14 => Some((3, 32)),
        15..=24 => Some((2, 28 * 32)),
        25 => Some((4, (CLAIMS + LANES) * 32)),
        26 => Some((5, LANES * 32)),
        _ => None,
    }
}

fn validate_record_fields(row: u8, payload: &[u8]) -> Result<(), Error> {
    for (value, bytes) in payload.chunks_exact(32).enumerate() {
        let x = WideExact::from_le_bytes(bytes).ok_or(Error::NonCanonical { row, value })?;
        if x.c1() != QM31::ZERO {
            return Err(Error::NonCanonical { row, value });
        }
    }
    Ok(())
}

/// Reject malformed framing and every noncanonical E limb before hashing.
/// UNPROVED P2 subset: reject any nonzero E high component at parse.
pub fn parse_record(row: u8, record: &[u8]) -> Result<&[u8], Error> {
    let (tag, size) = row_shape(row).ok_or(Error::InvalidRow)?;
    if record.len() != 5 + size {
        return Err(Error::Length { row });
    }
    if record[0] != tag {
        return Err(Error::Tag { row });
    }
    if u32::from_le_bytes([record[1], record[2], record[3], record[4]]) as usize != size {
        return Err(Error::Length { row });
    }
    let payload = &record[5..];
    if row >= 14 {
        validate_record_fields(row, payload)?;
    }
    Ok(payload)
}

pub fn record(row: u8, payload: &[u8]) -> Result<Vec<u8>, Error> {
    let (tag, size) = row_shape(row).ok_or(Error::InvalidRow)?;
    if payload.len() != size {
        return Err(Error::Length { row });
    }
    let mut out = Vec::with_capacity(5 + size);
    out.push(tag);
    out.extend_from_slice(&(size as u32).to_le_bytes());
    out.extend_from_slice(payload);
    parse_record(row, &out)?;
    Ok(out)
}

pub fn encode_values(values: impl IntoIterator<Item = WideExact>) -> Vec<u8> {
    let mut out = Vec::new();
    for value in values {
        out.extend_from_slice(&value.to_le_bytes());
    }
    out
}

pub fn decode_values<const N: usize>(row: u8, payload: &[u8]) -> Result<[WideExact; N], Error> {
    if payload.len() != 32 * N {
        return Err(Error::Length { row });
    }
    let mut out = [WideExact::ZERO; N];
    for (value, bytes) in payload.chunks_exact(32).enumerate() {
        out[value] = WideExact::from_le_bytes(bytes).ok_or(Error::NonCanonical { row, value })?;
    }
    Ok(out)
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
    pub(crate) fn row(&self) -> u8 {
        self.row
    }

    pub(crate) fn framed(&self) -> &'a [u8] {
        self.framed
    }

    pub(crate) fn payload(&self) -> &'a [u8] {
        &self.framed[5..]
    }

    /// Decode checked base-field limbs from a semantic record. The
    /// validation token proves the 16-byte high half is zero and the
    /// low QM31 encoding canonical, while this method still checks the
    /// requested range and record class.
    pub(crate) fn decode_k<const N: usize>(
        &self,
        offset_values: usize,
    ) -> Result<[QM31; N], Error> {
        if self.row < 14 {
            return Err(Error::InvalidRow);
        }
        let byte_offset = offset_values
            .checked_mul(32)
            .ok_or(Error::Length { row: self.row })?;
        let byte_len = N.checked_mul(32).ok_or(Error::Length { row: self.row })?;
        let end = byte_offset
            .checked_add(byte_len)
            .ok_or(Error::Length { row: self.row })?;
        let bytes = self
            .payload()
            .get(byte_offset..end)
            .ok_or(Error::Length { row: self.row })?;
        let mut out = [QM31::ZERO; N];
        for (value, part) in bytes.chunks_exact(32).enumerate() {
            out[value] = QM31::from_le_bytes(&part[..16]).ok_or(Error::NonCanonical {
                row: self.row,
                value: offset_values + value,
            })?;
        }
        Ok(out)
    }
}

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
    pub fn state(&self) -> [u8; 32] {
        self.state
    }
    pub fn next_row(&self) -> u8 {
        self.next_row
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
    fn sample_block(&mut self, row: u8, framed: &[u8]) -> Result<[u8; 32], Error> {
        if row != self.next_row {
            return Err(Error::RowOrder {
                expected: self.next_row,
                actual: row,
            });
        }
        parse_record(row, framed)?;
        self.sample_block_validated(row, framed)
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
    pub fn semantic(&mut self, row: u8, framed: &[u8]) -> Result<QM31, Error> {
        if row > 24 {
            return Err(Error::InvalidRow);
        }
        Ok(qm31_sample(&self.sample_block(row, framed)?))
    }
    /// R-B's one-block reference-circle map, including fixed fallback.
    /// The legacy Transcript method has a different parameter sampler.
    pub fn challenge_reference_circle_point(
        &mut self,
        row: u8,
        framed: &[u8],
    ) -> Result<SecureCirclePoint, Error> {
        let circle_row = match row {
            25 => CircleRow::First,
            26 => CircleRow::Second,
            _ => return Err(Error::InvalidRow),
        };
        Ok(circle_sample(&self.sample_block(row, framed)?, circle_row))
    }
}

/// Compact semantic wire: C1 root, followed by the 27 P1 records through
/// beforeZ1. No header, mask nonce, work nonce or opening suffix is read.
/// The opening owner consumes the returned row-27 state and both claims.
pub struct Prefix<'a> {
    pub c1_root: &'a [u8; 32],
    records: [&'a [u8]; 27],
}

fn parse_record_at<'a>(
    bytes: &'a [u8],
    row: u8,
    offset: usize,
) -> Result<(&'a [u8], usize), Error> {
    let length = 5 + row_shape(row).unwrap().1;
    let framed = bytes
        .get(offset..offset + length)
        .ok_or(Error::Length { row })?;
    parse_record(row, framed)?;
    Ok((framed, offset + length))
}

impl<'a> Prefix<'a> {
    pub fn parse(bytes: &'a [u8]) -> Result<Self, Error> {
        if bytes.len() < 32 {
            return Err(Error::Length { row: 0 });
        }
        let c1_root = match bytes[..32].try_into() {
            Ok(root) => root,
            Err(_) => return Err(Error::Length { row: 0 }),
        };
        let (r0, offset) = parse_record_at(bytes, 0, 32)?;
        let (r1, offset) = parse_record_at(bytes, 1, offset)?;
        let (r2, offset) = parse_record_at(bytes, 2, offset)?;
        let (r3, offset) = parse_record_at(bytes, 3, offset)?;
        let (r4, offset) = parse_record_at(bytes, 4, offset)?;
        let (r5, offset) = parse_record_at(bytes, 5, offset)?;
        let (r6, offset) = parse_record_at(bytes, 6, offset)?;
        let (r7, offset) = parse_record_at(bytes, 7, offset)?;
        let (r8, offset) = parse_record_at(bytes, 8, offset)?;
        let (r9, offset) = parse_record_at(bytes, 9, offset)?;
        let (r10, offset) = parse_record_at(bytes, 10, offset)?;
        let (r11, offset) = parse_record_at(bytes, 11, offset)?;
        let (r12, offset) = parse_record_at(bytes, 12, offset)?;
        let (r13, offset) = parse_record_at(bytes, 13, offset)?;
        let (r14, offset) = parse_record_at(bytes, 14, offset)?;
        let (r15, offset) = parse_record_at(bytes, 15, offset)?;
        let (r16, offset) = parse_record_at(bytes, 16, offset)?;
        let (r17, offset) = parse_record_at(bytes, 17, offset)?;
        let (r18, offset) = parse_record_at(bytes, 18, offset)?;
        let (r19, offset) = parse_record_at(bytes, 19, offset)?;
        let (r20, offset) = parse_record_at(bytes, 20, offset)?;
        let (r21, offset) = parse_record_at(bytes, 21, offset)?;
        let (r22, offset) = parse_record_at(bytes, 22, offset)?;
        let (r23, offset) = parse_record_at(bytes, 23, offset)?;
        let (r24, offset) = parse_record_at(bytes, 24, offset)?;
        let (r25, offset) = parse_record_at(bytes, 25, offset)?;
        let (r26, offset) = parse_record_at(bytes, 26, offset)?;
        if offset != bytes.len() {
            return Err(Error::TrailingBytes);
        }
        Ok(Self {
            c1_root,
            records: [
                r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17,
                r18, r19, r20, r21, r22, r23, r24, r25, r26,
            ],
        })
    }
    pub fn record(&self, row: u8) -> Result<&'a [u8], Error> {
        if row >= 27 {
            return Err(Error::InvalidRow);
        }
        Ok(self.records[row as usize])
    }
    pub fn payload(&self, row: u8) -> Result<&'a [u8], Error> {
        let framed = self.record(row)?;
        Ok(&framed[5..])
    }
    pub(crate) fn validated_record(&self, row: u8) -> Result<ValidatedRecord<'a>, Error> {
        Ok(ValidatedRecord {
            row,
            framed: self.record(row)?,
        })
    }
    /// Same row-25 decoder, with direct initialization of heap storage.
    pub fn point_claims_boxed(&self) -> Result<alloc::boxed::Box<PointClaims>, Error> {
        let payload = self.payload(25)?;
        if payload.len() != 32 * (CLAIMS + LANES) {
            return Err(Error::Length { row: 25 });
        }
        let mut out =
            aspis_core::r0::heap::uninit::<PointClaims>().map_err(|_| Error::Allocation)?;
        unsafe {
            let p = out.as_mut_ptr().cast::<WideExact>();
            for j in 0..CLAIMS {
                p.add(j).write(
                    WideExact::from_le_bytes(&payload[j * 32..(j + 1) * 32])
                        .ok_or(Error::NonCanonical { row: 25, value: j })?,
                );
            }
            Ok(out.assume_init())
        }
    }
    pub fn point_claims(&self) -> Result<PointClaims, Error> {
        let flat = decode_values::<CLAIMS>(25, &self.payload(25)?[..CLAIMS * 32])?;
        Ok(core::array::from_fn(|point| {
            core::array::from_fn(|lane| flat[point * LANES + lane])
        }))
    }
}

/// MSB-first semantic coordinates; reverse these for R-D's eqWeight.
pub fn statement_points(alpha: &[QM31; 10]) -> [[QM31; 10]; 3] {
    aspis_core::state_only_prefix::r0::statement_points(alpha)
}

pub use aspis_core::state_only_prefix::r0::Challenges;
/// Rows 0..14. Roots are the only commitment records; there is no helper
/// zero-sum/registry absorb between row 2 and theta.
#[inline(never)]
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

#[cfg(test)]
mod validated_tests {
    use super::*;

    #[derive(Clone, Copy)]
    struct TestDigest;
    impl aspis_core::Digest32 for TestDigest {
        fn digest(&self, parts: &[&[u8]]) -> [u8; 32] { test_hash(parts) }
    }

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

    fn valid_prefix_bytes() -> Vec<u8> {
        let mut bytes = alloc::vec![0u8; 32];
        for row in 0..27 {
            let size = row_shape(row).unwrap().1;
            bytes.extend_from_slice(&record(row, &alloc::vec![0; size]).unwrap());
        }
        bytes
    }

    #[test]
    fn validated_transcript_matches_checked_raw_path_for_every_row() {
        let bytes = valid_prefix_bytes();
        let prefix = Prefix::parse(&bytes).unwrap();
        let root = prefix.c1_root;
        let mut checked = SemanticTranscript::new(TestDigest, b"public", root).unwrap();
        let mut validated = SemanticTranscript::new(TestDigest, b"public", root).unwrap();

        for row in 0..27 {
            let raw = prefix.record(row).unwrap();
            let token = prefix.validated_record(row).unwrap();
            if row <= 24 {
                assert_eq!(
                    checked.semantic(row, raw),
                    validated.semantic_validated(token)
                );
            } else {
                assert_eq!(
                    checked.challenge_reference_circle_point(row, raw),
                    validated.circle_validated(token),
                );
            }
            assert_eq!(checked.state(), validated.state());
            assert_eq!(checked.next_row(), validated.next_row());
        }
    }
}

#[cfg(test)]
mod record_parser_tests {
    use super::*;
    use aspis_core::field::P;

    // Previous parser retained as a differential oracle, including the
    // original validation loop and exact error ordering.
    fn parse_record_loop_reference(row: u8, record: &[u8]) -> Result<&[u8], Error> {
        let (tag, size) = row_shape(row).ok_or(Error::InvalidRow)?;
        if record.len() != 5 + size {
            return Err(Error::Length { row });
        }
        if record[0] != tag {
            return Err(Error::Tag { row });
        }
        if u32::from_le_bytes(record[1..5].try_into().unwrap()) as usize != size {
            return Err(Error::Length { row });
        }
        let payload = &record[5..];
        if row >= 14 {
            for (value, bytes) in payload.chunks_exact(32).enumerate() {
                let x =
                    WideExact::from_le_bytes(bytes).ok_or(Error::NonCanonical { row, value })?;
                if x.c1() != QM31::ZERO {
                    return Err(Error::NonCanonical { row, value });
                }
            }
        }
        Ok(payload)
    }

    fn raw_frame(row: u8) -> Vec<u8> {
        let (tag, size) = row_shape(row).unwrap();
        let mut framed = alloc::vec![0u8; 5 + size];
        framed[0] = tag;
        framed[1..5].copy_from_slice(&(size as u32).to_le_bytes());
        if row == 2 {
            // Commitment roots are arbitrary bytes, not canonical field limbs.
            framed[5..].fill(255);
        } else if row >= 14 {
            for (value, bytes) in framed[5..].chunks_exact_mut(32).enumerate() {
                for limb in 0..4 {
                    let n = if value % 2 == 0 {
                        P - 1
                    } else {
                        1 + limb as u32
                    };
                    bytes[4 * limb..4 * limb + 4].copy_from_slice(&n.to_le_bytes());
                }
            }
        }
        framed
    }

    fn check_error(row: u8, frame: &[u8], error: Error) {
        assert_eq!(parse_record_loop_reference(row, frame), Err(error));
        assert_eq!(parse_record(row, frame), Err(error));
    }

    #[test]
    fn parser_helper_preserves_all_shapes_and_framing_errors() {
        let mut shapes = [(0u8, 0usize); 27];
        shapes[2] = (1, 32);
        shapes[14] = (3, 32);
        shapes[15..25].fill((2, 896));
        shapes[25] = (4, 3712);
        shapes[26] = (5, 928);
        for row in 0..=u8::MAX {
            assert_eq!(row_shape(row), shapes.get(row as usize).copied());
            if row > 26 {
                check_error(row, &[], Error::InvalidRow);
                check_error(row, &[255; 5], Error::InvalidRow);
                continue;
            }
            let framed = raw_frame(row);
            let actual = parse_record(row, &framed).unwrap();
            assert_eq!(Ok(actual), parse_record_loop_reference(row, &framed));
            assert_eq!(actual, &framed[5..]);
            assert_eq!(actual.as_ptr(), framed[5..].as_ptr());
            for length in 0..5 {
                check_error(row, &framed[..length], Error::Length { row });
            }
            check_error(row, &framed[..framed.len() - 1], Error::Length { row });
            let mut extra = framed.clone();
            extra.push(0);
            check_error(row, &extra, Error::Length { row });
            let mut bad_tag = framed.clone();
            bad_tag[0] ^= 255;
            bad_tag[1..5].fill(255);
            check_error(row, &bad_tag, Error::Tag { row });
            let mut bad_length = framed.clone();
            bad_length[1..5].fill(255);
            check_error(row, &bad_length, Error::Length { row });
        }
    }

    #[test]
    fn parser_helper_preserves_canonicality_and_first_failing_value() {
        for row in 14..=26 {
            let framed = raw_frame(row);
            let values = (framed.len() - 5) / 32;
            for value in 0..values {
                for limb in 0..8 {
                    for bad in [P, u32::MAX] {
                        let mut malformed = framed.clone();
                        let offset = 5 + 32 * value + 4 * limb;
                        malformed[offset..offset + 4].copy_from_slice(&bad.to_le_bytes());
                        check_error(row, &malformed, Error::NonCanonical { row, value });
                    }
                }
                for limb in 4..8 {
                    let mut high_nonzero = framed.clone();
                    let offset = 5 + 32 * value + 4 * limb;
                    high_nonzero[offset..offset + 4].copy_from_slice(&1u32.to_le_bytes());
                    check_error(row, &high_nonzero, Error::NonCanonical { row, value });
                }
                if value + 1 < values {
                    let mut two_errors = framed.clone();
                    let first_high = 5 + 32 * value + 16;
                    two_errors[first_high..first_high + 4].copy_from_slice(&1u32.to_le_bytes());
                    let later_noncanonical = 5 + 32 * (value + 1);
                    two_errors[later_noncanonical..later_noncanonical + 4]
                        .copy_from_slice(&P.to_le_bytes());
                    check_error(row, &two_errors, Error::NonCanonical { row, value });
                }
            }
        }
    }
}

#[cfg(test)]
mod prefix_parser_tests {
    use super::*;
    use aspis_core::field::P;

    // Freeze the complete pre-refactor parser, including its error ordering.
    fn parse_reference<'a>(bytes: &'a [u8]) -> Result<Prefix<'a>, Error> {
        if bytes.len() < 32 {
            return Err(Error::Length { row: 0 });
        }
        let c1_root = bytes[..32].try_into().unwrap();
        let mut records = [&[][..]; 27];
        let mut offset = 32;
        for row in 0..27u8 {
            let length = 5 + row_shape(row).unwrap().1;
            let framed = bytes
                .get(offset..offset + length)
                .ok_or(Error::Length { row })?;
            parse_record(row, framed)?;
            records[row as usize] = framed;
            offset += length;
        }
        if offset != bytes.len() {
            return Err(Error::TrailingBytes);
        }
        Ok(Prefix { c1_root, records })
    }
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
    fn prefix_aggregate_preserves_slices_and_all_truncations() {
        let (bytes, offsets) = fixture();
        let actual = Prefix::parse(&bytes).unwrap();
        let expected = parse_reference(&bytes).unwrap();
        assert_eq!(actual.c1_root, expected.c1_root);
        assert_eq!(actual.c1_root.as_ptr(), bytes.as_ptr());
        let mut next_offset = 32;
        // Independently inspect each helper result as well as the final array.
        for row in 0..27u8 {
            let start = offsets[row as usize];
            let end = offsets[row as usize + 1];
            let frame = actual.record(row).unwrap();
            assert_eq!(frame, expected.record(row).unwrap());
            assert_eq!(frame, &bytes[start..end]);
            assert_eq!(frame.as_ptr(), bytes[start..end].as_ptr());
            let (single, next) = parse_record_at(&bytes, row, next_offset).unwrap();
            assert_eq!(single.as_ptr(), frame.as_ptr());
            assert_eq!(single.len(), frame.len());
            assert_eq!(next, end);
            next_offset = next;
            let payload = actual.payload(row).unwrap();
            assert_eq!(payload, expected.payload(row).unwrap());
            assert_eq!(payload.as_ptr(), bytes[start + 5..end].as_ptr());
            let token = actual.validated_record(row).unwrap();
            assert_eq!(token.row(), row);
            assert_eq!(token.framed().as_ptr(), frame.as_ptr());
            assert_eq!(token.payload(), payload);
        }
        assert_eq!(next_offset, bytes.len());
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
            two_errors[payload_start + 16..payload_start + 20].copy_from_slice(&1u32.to_le_bytes());
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

// Owned state: the consumed byte prefix never borrows across recursion.
// Short suffixes follow chunks_exact(32): they are not validated.
#[cfg(any(kani,aeneas_ref))]
pub mod fields20 {
    use alloc::vec::Vec;
    use aspis_core::field::{WideExact,QM31};
    use super::Error;
    pub fn validate(row:u8,payload:Vec<u8>,value:usize)->Result<(),Error> {
        if payload.len()<32 { return Ok(()); }
        let bytes=&payload[..32];
        let x=match WideExact::from_le_bytes(bytes) { Some(x)=>x, None=>return Err(Error::NonCanonical {row,value}) };
        if x.c1()!=QM31::ZERO { return Err(Error::NonCanonical {row,value}); }
        let tail=payload[32..].to_vec();
        validate(row,tail,value+1)
    }
}

// Fresh owned transcript state for every row. Hash reads still use the
// unchanged source sample_block_validated; no new hash implementation.
#[cfg(any(kani,aeneas_ref))]
pub mod semantic20 {
    use alloc::vec::Vec;
    use aspis_core::{Digest32,field::QM31};
    use super::{Error,SemanticTranscript,row_shape,fields20};
    pub fn checked(row:u8,record:&[u8])->Result<(),Error> {
        let (tag,size)=match row_shape(row) {Some(shape)=>shape,None=>return Err(Error::InvalidRow)};
        if record.len()!=5+size {return Err(Error::Length{row});}
        if record[0]!=tag {return Err(Error::Tag{row});}
        if u32::from_le_bytes([record[1],record[2],record[3],record[4]]) as usize !=size {
            return Err(Error::Length{row});
        }
        if row>=14 {
            match fields20::validate(row,record[5..].to_vec(),0) {Ok(())=>(),Err(e)=>return Err(e)}
        }
        Ok(())
    }
    pub fn semantic<H:Digest32>(mut state:SemanticTranscript<H>,row:u8,record:Vec<u8>)
        ->(Result<QM31,Error>,SemanticTranscript<H>) {
        if row>24 {return (Err(Error::InvalidRow),state);}
        if row!=state.next_row {
            return (Err(Error::RowOrder{expected:state.next_row,actual:row}),state);
        }
        match checked(row,&record) {Ok(())=>(),Err(e)=>return (Err(e),state)}
        let block=match state.sample_block_validated(row,&record) {
            Ok(block)=>block,Err(e)=>return (Err(e),state)
        };
        (Ok(crate::sampler::qm31_sample(&block)),state)
    }
    pub fn rows<H:Digest32>(state:SemanticTranscript<H>,records:Vec<Vec<u8>>,row:usize,
        mut sem:[QM31;25])->(Result<[QM31;25],Error>,SemanticTranscript<H>) {
        if row==25 {return (Ok(sem),state);}
        let (value,state)=semantic(state,row as u8,records[row].clone());
        match value {
            Err(e)=>(Err(e),state),
            Ok(value)=>{sem[row]=value;rows(state,records,row.wrapping_add(1),sem)}
        }
    }
}

// Explicit field-cell fuel for proof-only Kani substitution. The generic
// owned recursion remains the retained reference; Lean proves equality under
// its existing length bound before this helper is used in a caller gate.
#[cfg(any(kani,aeneas_ref))]
pub mod fields29 {
    use alloc::vec::Vec;
    use aspis_core::field::{WideExact,QM31};
    use super::Error;
    pub fn finite(row:u8,payload:Vec<u8>,value:usize,remaining:usize)->Result<(),Error> {
        if remaining==0 {return Ok(());}
        if payload.len()<32 {return Ok(());}
        let bytes=&payload[..32];
        let x=match WideExact::from_le_bytes(bytes) {Some(x)=>x,None=>return Err(Error::NonCanonical{row,value})};
        if x.c1()!=QM31::ZERO {return Err(Error::NonCanonical{row,value});}
        let tail=payload[32..].to_vec();
        finite(row,tail,value.wrapping_add(1),remaining.wrapping_sub(1))
    }
}

#[cfg(kani)]
pub(crate) mod pdict_error_contracts {
    use super::Error;
    pub(crate) fn arbitrary_error() -> Error {
        let tag: u8 = kani::any();
        kani::assume(tag < 12);
        match tag {
            0 => Error::Allocation,
            1 => Error::RowOrder { expected: kani::any(), actual: kani::any() },
            2 => Error::InvalidRow,
            3 => Error::Tag { row: kani::any() },
            4 => Error::Length { row: kani::any() },
            5 => Error::NonCanonical { row: kani::any(), value: kani::any() },
            6 => Error::Boundary { round: kani::any() },
            7 => Error::Terminal,
            8 => Error::EqualCirclePoints,
            9 => Error::TrailingBytes,
            10 => Error::Public,
            _ => Error::ActivePole,
        }
    }
    #[kani::proof]
    fn complete_wire_error_equality() {
        let a = arbitrary_error();
        let b = arbitrary_error();
        let expected = match (a,b) {
            (Error::Allocation,Error::Allocation) => true,
            (Error::RowOrder { expected:a,actual:b },Error::RowOrder { expected:c,actual:d }) => a==c && b==d,
            (Error::InvalidRow,Error::InvalidRow) => true,
            (Error::Tag { row:a },Error::Tag { row:b }) => a==b,
            (Error::Length { row:a },Error::Length { row:b }) => a==b,
            (Error::NonCanonical { row:a,value:b },Error::NonCanonical { row:c,value:d }) => a==c && b==d,
            (Error::Boundary { round:a },Error::Boundary { round:b }) => a==b,
            (Error::Terminal,Error::Terminal) => true,
            (Error::EqualCirclePoints,Error::EqualCirclePoints) => true,
            (Error::TrailingBytes,Error::TrailingBytes) => true,
            (Error::Public,Error::Public) => true,
            (Error::ActivePole,Error::ActivePole) => true,
            _ => false,
        };
        assert_eq!(a==b,expected);
    }
}

#[cfg(kani)]
mod pdict_typenum_contracts {
    use sha2::digest::typenum::{UTerm,B0,B1,Equal,Greater,Unsigned,Bit};
    #[kani::proof]
    fn terminal_numeric_entries() {
        assert_eq!(UTerm::to_isize(),0); assert_eq!(UTerm::ISIZE,0);
        assert_eq!(UTerm::to_i64(),0); assert_eq!(UTerm::I64,0);
        assert_eq!(UTerm::to_i32(),0); assert_eq!(UTerm::I32,0);
        assert_eq!(UTerm::to_i16(),0); assert_eq!(UTerm::I16,0);
        assert_eq!(UTerm::to_i8(),0); assert_eq!(UTerm::I8,0);
        assert_eq!(UTerm::to_usize(),0); assert_eq!(UTerm::USIZE,0);
        assert_eq!(UTerm::to_u64(),0); assert_eq!(UTerm::U64,0);
        assert_eq!(UTerm::to_u32(),0); assert_eq!(UTerm::U32,0);
        assert_eq!(UTerm::to_u16(),0); assert_eq!(UTerm::U16,0);
        assert_eq!(UTerm::to_u8(),0); assert_eq!(UTerm::U8,0);
        let t=UTerm::default(); assert_eq!(t.clone(),t);
        assert!(B1::to_bool()); assert!(B1::BOOL);
        assert_eq!(B1::to_u8(),1); assert_eq!(B1::U8,1);
        let b1=B1::new(); assert_eq!(b1,B1::default()); assert_eq!(b1.clone(),b1);
        assert!(!B0::to_bool()); assert!(!B0::BOOL);
        assert_eq!(B0::to_u8(),0); assert_eq!(B0::U8,0);
        let b0=B0::new(); assert_eq!(b0,B0::default()); assert_eq!(b0.clone(),b0);
        assert_eq!(<Equal as sha2::digest::typenum::Ord>::to_ordering(),core::cmp::Ordering::Equal);
        assert_eq!(<Greater as sha2::digest::typenum::Ord>::to_ordering(),core::cmp::Ordering::Greater);
    }
}

#[cfg(kani)]
mod pdict_numeric_contracts {
    use sha2::digest::typenum::{Unsigned,Bit,UInt,B0,B1,consts::*};
    fn numeric<U:Unsigned,B:Bit>() {
        assert_eq!(UInt::<U,B>::to_isize(), (B::to_u8() as isize) | U::to_isize().wrapping_shl(1));
        assert_eq!(UInt::<U,B>::ISIZE, (B::U8 as isize) | U::ISIZE.wrapping_shl(1));
        assert_eq!(UInt::<U,B>::to_i64(), (B::to_u8() as i64) | U::to_i64().wrapping_shl(1));
        assert_eq!(UInt::<U,B>::I64, (B::U8 as i64) | U::I64.wrapping_shl(1));
        assert_eq!(UInt::<U,B>::to_i32(), (B::to_u8() as i32) | U::to_i32().wrapping_shl(1));
        assert_eq!(UInt::<U,B>::I32, (B::U8 as i32) | U::I32.wrapping_shl(1));
        assert_eq!(UInt::<U,B>::to_i16(), (B::to_u8() as i16) | U::to_i16().wrapping_shl(1));
        assert_eq!(UInt::<U,B>::I16, (B::U8 as i16) | U::I16.wrapping_shl(1));
        assert_eq!(UInt::<U,B>::to_i8(), (B::to_u8() as i8) | U::to_i8().wrapping_shl(1));
        assert_eq!(UInt::<U,B>::I8, (B::U8 as i8) | U::I8.wrapping_shl(1));
        assert_eq!(UInt::<U,B>::to_usize(), (B::to_u8() as usize) | U::to_usize().wrapping_shl(1));
        assert_eq!(UInt::<U,B>::USIZE, (B::U8 as usize) | U::USIZE.wrapping_shl(1));
        assert_eq!(UInt::<U,B>::to_u64(), (B::to_u8() as u64) | U::to_u64().wrapping_shl(1));
        assert_eq!(UInt::<U,B>::U64, (B::U8 as u64) | U::U64.wrapping_shl(1));
        assert_eq!(UInt::<U,B>::to_u32(), (B::to_u8() as u32) | U::to_u32().wrapping_shl(1));
        assert_eq!(UInt::<U,B>::U32, (B::U8 as u32) | U::U32.wrapping_shl(1));
        assert_eq!(UInt::<U,B>::to_u16(), (B::to_u8() as u16) | U::to_u16().wrapping_shl(1));
        assert_eq!(UInt::<U,B>::U16, (B::U8 as u16) | U::U16.wrapping_shl(1));
        assert_eq!(UInt::<U,B>::to_u8(), (B::to_u8() as u8) | U::to_u8().wrapping_shl(1));
        assert_eq!(UInt::<U,B>::U8, (B::U8 as u8) | U::U8.wrapping_shl(1));
    }
    #[kani::proof]
    fn numeric_source_recursion() {
        numeric::<U0,B0>(); numeric::<U0,B1>();
        numeric::<U1,B0>(); numeric::<U1,B1>();
        numeric::<U2,B0>(); numeric::<U2,B1>();
        numeric::<U4,B0>(); numeric::<U4,B1>();
        numeric::<U8,B0>(); numeric::<U8,B1>();
        numeric::<U16,B0>(); numeric::<U16,B1>();
        numeric::<U32,B0>(); numeric::<U32,B1>();
        numeric::<U64,B0>(); numeric::<U64,B1>();
        numeric::<U128,B0>(); numeric::<U128,B1>();
        numeric::<U256,B0>(); numeric::<U256,B1>();
        numeric::<U512,B0>(); numeric::<U512,B1>();
    }
}

#[cfg(kani)]
mod pdict_comparison_contracts {
    use sha2::digest::typenum::{UTerm,UInt,B0,B1,Equal,Greater,Less,consts::U512};
    use sha2::digest::typenum::private::{PrivateCmp,IsLessOrEqualPrivate,IsLessPrivate};
    #[kani::proof]
    fn terminal_comparison_entries() {
        assert_eq!(UTerm.private_cmp(&UTerm,Equal),Equal);
        assert_eq!(UTerm.private_cmp(&UTerm,Greater),Greater);
        assert_eq!(UTerm.private_cmp(&UTerm,Less),Less);
        assert_eq!(UTerm.private_cmp(&UInt::<U512,B0>::default(),Equal),Less);
        assert_eq!(UTerm.private_cmp(&UInt::<U512,B1>::default(),Greater),Less);
        assert_eq!(UTerm.private_cmp(&UInt::<UTerm,B0>::default(),Less),Less);
        let a:u64=kani::any(); let b:u64=kani::any();
        assert_eq!(a.is_less_or_equal_private(b,Equal),B1);
        assert_eq!(a.is_less_private(b,Less),B1);
    }
}

#[cfg(kani)]
mod pdict_primitive_contracts {
    use sha2::digest::{block_buffer::{BlockBuffer,Eager},typenum::consts::U64};
    #[kani::proof]
    fn truncation_and_eager_default() {
        use sha2::digest::core_api::{TruncSide,VariableOutputCore};
        assert!(matches!(<sha2::Sha256VarCore as VariableOutputCore>::TRUNC_SIDE,TruncSide::Left));
        let _:Eager=Default::default();
        assert_eq!(core::mem::size_of::<Eager>(),0);
    }
    #[kani::proof]
    #[kani::unwind(67)]
    fn eager_sha_block_boundary() {
        let data:[u8;65]=kani::any();
        let pos:usize=kani::any(); kani::assume(pos<=65);
        let buffer=BlockBuffer::<U64,Eager>::try_new(&data[..pos]);
        assert_eq!(buffer.is_ok(),pos<64);
        if let Ok(buffer)=buffer { assert_eq!(buffer.get_pos(),pos); }
    }
    #[kani::proof]
    fn slice_and_shared_as_ref() {
        let data:[u8;4]=kani::any();
        let n:usize=kani::any(); kani::assume(n<=4);
        let slice=&data[..n];
        let returned:&[u8]=slice.as_ref();
        assert!(core::ptr::eq(slice,returned));
        let value:u64=kani::any();
        struct Probe { value:u64 }
        impl AsRef<u64> for Probe { fn as_ref(&self)->&u64 { &self.value } }
        let probe=Probe{value}; let shared=&probe;
        let actual:&u64=shared.as_ref();
        assert!(core::ptr::eq(actual,&probe.value));
        assert_eq!(*actual,value);
    }
}

#[cfg(kani)]
mod pdict_ordering_contracts {
    use sha2::digest::typenum::{B0,B1,consts::*,IsLess,IsLessOrEqual};
    #[kani::proof]
    fn source_ordering_instances() {
        assert_eq!(U64::default().is_less(U256::default()),B1);
        assert_eq!(U64::default().is_less_or_equal(U256::default()),B1);
        assert_eq!(U64::default().is_less(U64::default()),B0);
        assert_eq!(U64::default().is_less_or_equal(U64::default()),B1);
        assert_eq!(U512::default().is_less(U256::default()),B0);
        assert_eq!(U512::default().is_less_or_equal(U256::default()),B0);
    }
}

#[cfg(kani)]
mod pdict_representation_contracts {
    #[kani::proof]
    fn f64_raw_bit_roundtrip() {
        let bits:u64=kani::any();
        assert_eq!(f64::from_bits(bits).to_bits(),bits);
    }
    #[kani::proof]
    fn uint_default_clone_all_scalar_fields() {
        use core::sync::atomic::{AtomicU8,Ordering};
        use sha2::digest::typenum::UInt;
        static STEP:AtomicU8=AtomicU8::new(0);
        #[derive(Clone,Copy,Debug,PartialEq,Eq)] struct Upper(u64);
        #[derive(Clone,Copy,Debug,PartialEq,Eq)] struct Lower(u8);
        impl Default for Upper { fn default()->Self {
            assert_eq!(STEP.fetch_add(1,Ordering::Relaxed),0); Self(kani::any())
        }}
        impl Default for Lower { fn default()->Self {
            assert_eq!(STEP.fetch_add(1,Ordering::Relaxed),1); Self(kani::any())
        }}
        STEP.store(0,Ordering::Relaxed);
        let native=UInt::<Upper,Lower>::default();
        assert_eq!(STEP.load(Ordering::Relaxed),2);
        assert_eq!(native.clone(),native);
    }
}

#[cfg(kani)]
mod pdict_error_value_contracts {
    #[kani::proof]
    fn complete_getrandom_error_value_codec() {
        let raw=core::num::NonZeroI32::new(kani::any())
            .unwrap_or(core::num::NonZeroI32::new(1).unwrap());
        assert_eq!(core::mem::size_of::<getrandom::Error>(),4);
        assert_eq!(core::mem::align_of::<getrandom::Error>(),4);
        // Every nonzero code is a valid value of the sole NonZeroI32 field.
        // No OS function, entropy provider or destructor is stubbed or called.
        let error:getrandom::Error=unsafe { core::mem::transmute(raw) };
        let cloned=error.clone(); assert_eq!(error,cloned);
        let copied=error;
        let encoded:core::num::NonZeroI32=unsafe { core::mem::transmute(copied) };
        assert_eq!(encoded,raw);
    }
}

#[cfg(kani)]
mod pdict_options_contracts {
    use std::fs::OpenOptions;
    use std::os::unix::fs::OpenOptionsExt;
    #[derive(Clone,Copy,Debug,PartialEq,Eq)]
    struct State {
        read:bool, write:bool, append:bool, truncate:bool, create:bool,
        create_new:bool, custom_flags:i32, mode:u32,
    }
    // Complete primitive-field view of the pinned Unix OpenOptions schema.
    // Reading a bool at an incorrect offset is checked by Kani's validity rules.
    fn view(options:&OpenOptions)->State {
        assert_eq!(core::mem::size_of::<OpenOptions>(),core::mem::size_of::<State>());
        assert_eq!(core::mem::align_of::<OpenOptions>(),core::mem::align_of::<State>());
        assert!(!core::mem::needs_drop::<OpenOptions>());
        unsafe { core::mem::transmute_copy(options) }
    }
    fn arbitrary()->(OpenOptions,State) {
        let state=State{read:kani::any(),write:kani::any(),append:kani::any(),
            truncate:kani::any(),create:kani::any(),create_new:kani::any(),
            custom_flags:kani::any(),mode:kani::any()};
        let mut options=OpenOptions::new();
        options.read(state.read).write(state.write).append(state.append)
            .truncate(state.truncate).create(state.create).create_new(state.create_new)
            .custom_flags(state.custom_flags).mode(state.mode);
        assert_eq!(view(&options),state);
        (options,state)
    }
    #[kani::proof]
    fn complete_options_state_and_new() {
        let options=OpenOptions::new();
        assert_eq!(view(&options),State{read:false,write:false,append:false,
            truncate:false,create:false,create_new:false,custom_flags:0,mode:0o666});
        let _=arbitrary();
    }
    #[kani::proof]
    fn write_loan_and_frame() {
        let (mut options,mut expected)=arbitrary();
        let flag:bool=kani::any();
        let receiver=&mut options as *mut OpenOptions;
        let returned=options.write(flag) as *mut OpenOptions;
        assert_eq!(receiver,returned);
        expected.write=flag; assert_eq!(view(&options),expected);
    }
    #[kani::proof]
    fn create_new_loan_and_frame() {
        let (mut options,mut expected)=arbitrary();
        let flag:bool=kani::any();
        let receiver=&mut options as *mut OpenOptions;
        let returned=options.create_new(flag) as *mut OpenOptions;
        assert_eq!(receiver,returned);
        expected.create_new=flag; assert_eq!(view(&options),expected);
    }
    #[kani::proof]
    fn mode_loan_and_frame() {
        let (mut options,mut expected)=arbitrary();
        let mode:u32=kani::any();
        let receiver=&mut options as *mut OpenOptions;
        let returned=options.mode(mode) as *mut OpenOptions;
        assert_eq!(receiver,returned);
        expected.mode=mode; assert_eq!(view(&options),expected);
    }
    #[kani::proof]
    #[kani::unwind(6)]
    fn path_short_bytes_and_shared_view() {
        use std::os::unix::ffi::OsStringExt;
        use std::path::{Path,PathBuf};
        let bytes:[u8;4]=kani::any(); let len:usize=kani::any(); kani::assume(len<=4);
        let owned=std::ffi::OsString::from_vec(bytes[..len].to_vec());
        let buf=PathBuf::from(owned);
        let a=buf.as_path(); let b:&Path=buf.as_ref(); let c:&Path=&*buf;
        assert!(core::ptr::eq(a,b)); assert!(core::ptr::eq(a,c));
        assert!(core::ptr::eq(a,a.as_ref()));
        assert_eq!(a.as_os_str().as_encoded_bytes(),&bytes[..len]);
    }
    #[kani::proof]
    fn native_layout_fields_and_alignment() {
        let shift:u32=kani::any(); kani::assume(shift<64);
        let size:usize=kani::any(); let align=1usize<<shift;
        if let Ok(layout)=std::alloc::Layout::from_size_align(size,align) {
            assert_eq!(layout.size(),size); assert_eq!(layout.align(),align);
        }
        let empty=std::alloc::Layout::from_size_align(0,align).unwrap();
        assert_eq!(empty.size(),0); assert_eq!(empty.align(),align);
    }
}

#[cfg(kani)]
mod pdict_resume_contracts {
    #[kani::proof]
    fn generic_array32_native_order() {
        let input: [u8;32] = kani::any();
        let native: sha2::digest::generic_array::GenericArray<u8,sha2::digest::consts::U32> = input.into();
        let output: [u8;32] = native.into();
        assert!(output == input);
    }

    #[kani::proof]
    fn formatter_preserves_sink_error() {
        use std::fmt::{self,Write};
        struct Probe;
        impl fmt::Debug for Probe {
            fn fmt(&self, f:&mut fmt::Formatter<'_>)->fmt::Result { f.write_str("x") }
        }
        struct Sink { fail:bool, called:bool }
        impl Write for Sink {
            fn write_str(&mut self,s:&str)->fmt::Result {
                assert!(s=="x"); self.called=true;
                if self.fail {Err(fmt::Error)} else {Ok(())}
            }
        }
        let fail:bool=kani::any();
        let mut sink=Sink{fail,called:false};
        let result=write!(&mut sink,"{:?}",Probe);
        assert!(sink.called);
        assert!(result.is_err()==fail);
    }

    #[kani::proof]
    fn io_error_simple_roundtrip() {
        use std::io::{Error,ErrorKind};
        let choice:bool=kani::any();
        let kind=if choice {ErrorKind::AlreadyExists} else {ErrorKind::Other};
        let error=Error::from(kind);
        assert!(error.kind()==kind);
        assert!(error.raw_os_error().is_none());
        assert!(error.get_ref().is_none());
    }
}

#[cfg(kani)]
mod pdict_array_fields {
    #[repr(C)]
    #[derive(Clone,Copy)]
    struct Even<U> { parent1:U,parent2:U }
    #[repr(C)]
    #[derive(Clone,Copy)]
    struct Odd { parent1:[u8;0],parent2:[u8;0],data:u8 }
    type Fields = Even<Even<Even<Even<Even<Odd>>>>>;
    #[kani::proof]
    fn native_conversion_matches_extracted_fields() {
        use sha2::digest::{generic_array::GenericArray,consts::U32};
        let input:[u8;32]=kani::any();
        let native:GenericArray<u8,U32>=input.into();
        // Both layouts are pinned repr(C), scalar-only, size32/alignment1.
        // Every possible bit pattern is initialized and valid for both types.
        let fields:Fields=unsafe{core::mem::transmute(native.clone())};
        let index:usize=kani::any();kani::assume(index<32);
        let f=if index<16{fields.parent1}else{fields.parent2};
        let f=if index%16<8{f.parent1}else{f.parent2};
        let f=if index%8<4{f.parent1}else{f.parent2};
        let f=if index%4<2{f.parent1}else{f.parent2};
        let f=if index%2==0{f.parent1}else{f.parent2};
        let output:[u8;32]=native.into();
        assert!(output[index]==f.data);
        assert!(output[index]==input[index]);
    }
}

#[cfg(kani)]
mod pdict_resource_diagnostics {
    #[kani::proof]
    fn file_is_owned_resource_not_plain_integer() {
        use std::fs::File;
        use std::os::fd::RawFd;
        assert!(core::mem::size_of::<File>()==core::mem::size_of::<RawFd>());
        assert!(core::mem::align_of::<File>()==core::mem::align_of::<RawFd>());
        assert!(core::mem::needs_drop::<File>());
        assert!(!core::mem::needs_drop::<RawFd>());
    }
    #[kani::proof]
    fn io_error_all_os_codes() {
        let code:i32=kani::any();
        let error=std::io::Error::from_raw_os_error(code);
        assert!(error.raw_os_error()==Some(code));
        assert!(error.get_ref().is_none());
    }
    #[kani::proof]
    fn io_custom_payload_and_drop() {
        use std::{io::Error,sync::atomic::{AtomicUsize,Ordering}};
        static DROPS:AtomicUsize=AtomicUsize::new(0);
        #[derive(Debug)] struct Payload(i32);
        impl core::fmt::Display for Payload {
            fn fmt(&self,f:&mut core::fmt::Formatter<'_>)->core::fmt::Result {f.write_str("payload")}
        }
        impl std::error::Error for Payload {}
        impl Drop for Payload {fn drop(&mut self){DROPS.fetch_add(1,Ordering::SeqCst);}}
        DROPS.store(0,Ordering::SeqCst);
        let value:i32=kani::any();
        let error=Error::other(Payload(value));
        assert!(error.raw_os_error().is_none());
        assert!(error.get_ref().unwrap().downcast_ref::<Payload>().unwrap().0==value);
        assert!(DROPS.load(Ordering::SeqCst)==0);
        drop(error);
        assert!(DROPS.load(Ordering::SeqCst)==1);
    }
}

#[cfg(kani)]
mod pdict_salt_clear {
    #[kani::proof]
    fn complete_cell_zero_and_frame() {
        struct Frame { before:u64,cell:[u8;32],after:u64 }
        let before:u64=kani::any();let after:u64=kani::any();
        let mut frame=Frame{before,cell:kani::any(),after};
        crate::host_commitment::clear_private_salt(&mut frame.cell);
        assert!(frame.cell==[0;32]);
        assert!(frame.before==before);
        assert!(frame.after==after);
    }
}
