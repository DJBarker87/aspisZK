//! UNPROVED COST PROBE. P2 D14-content wire; expanded row 25, isolated from the S4 gate.

use crate::sampler::{CircleRow, circle_sample, qm31_sample};
use alloc::vec::Vec;
use aspis_core::circle::SecureCirclePoint;
use aspis_core::field::{QM31, WideExact};
use aspis_core::transcript::HashFn;

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
    Public,
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
    if u32::from_le_bytes(record[1..5].try_into().unwrap()) as usize != size {
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
pub struct SemanticTranscript {
    state: [u8; 32],
    hash: HashFn,
    next_row: u8,
}

impl SemanticTranscript {
    pub fn new(hash: HashFn, public_bytes: &[u8], c1_root: &[u8; 32]) -> Result<Self, Error> {
        let length = u32::try_from(public_bytes.len()).map_err(|_| Error::Public)?;
        Ok(Self {
            state: hash(&[DOMAIN, &[0], &length.to_le_bytes(), public_bytes, c1_root]),
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
        let absorbed = (self.hash)(&[&self.state, &[0, 0xa0 + row], framed]);
        let block = (self.hash)(&[&absorbed, &[1]]);
        self.state = (self.hash)(&[&absorbed, &[2]]);
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
impl<'a> Prefix<'a> {
    pub fn parse(bytes: &'a [u8]) -> Result<Self, Error> {
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
        Ok(Self { c1_root, records })
    }
    pub fn record(&self, row: u8) -> Result<&'a [u8], Error> {
        self.records
            .get(row as usize)
            .copied()
            .ok_or(Error::InvalidRow)
    }
    pub fn payload(&self, row: u8) -> Result<&'a [u8], Error> {
        self.records
            .get(row as usize)
            .map(|framed| &framed[5..])
            .ok_or(Error::InvalidRow)
    }
    pub(crate) fn validated_record(&self, row: u8) -> Result<ValidatedRecord<'a>, Error> {
        Ok(ValidatedRecord { row, framed: self.record(row)? })
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
pub fn begin(
    prefix: &Prefix<'_>,
    transcript: &mut SemanticTranscript,
) -> Result<Challenges, Error> {
    let lambda = transcript.semantic_validated(prefix.validated_record(0)?)?;
    let chi = transcript.semantic_validated(prefix.validated_record(1)?)?;
    let theta = transcript.semantic_validated(prefix.validated_record(2)?)?;
    let mut zc = [QM31::ZERO; 10];
    for (i, value) in zc.iter_mut().enumerate() {
        *value = transcript.semantic_validated(prefix.validated_record(3 + i as u8)?)?;
    }
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
        let mut checked = SemanticTranscript::new(test_hash, b"public", root).unwrap();
        let mut validated = SemanticTranscript::new(test_hash, b"public", root).unwrap();

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
