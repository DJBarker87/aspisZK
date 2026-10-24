//! UNPROVED COST PROBE. Isolated S4 wire/transcript copy; K-only parse.

    use aspis_core::circle::SecureCirclePoint;
    use aspis_core::field::{WideExact, QM31};
    use crate::sampler::{circle_sample, qm31_sample, CircleRow};
    use aspis_core::transcript::HashFn;
    use alloc::vec::Vec;

    #[cfg(not(feature = "private-leaf-salts"))]
    pub const DOMAIN: &[u8] = b"aspis:r0:20261009:v1";
    #[cfg(feature = "private-leaf-salts")]
    pub const DOMAIN: &[u8] = b"UNPROVED:R1:PRIVATE-SALTED:SEMANTIC:P3";
    pub const LANES: usize = 29;
    pub const POINTS: usize = 3;
    pub const CLAIMS: usize = POINTS * LANES;
    pub const C1_LANES: [usize; 27] = [
        0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
        25, 28,
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
            25 => Some((4, CLAIMS * 32)),
            26 => Some((5, LANES * 32)),
            _ => None,
        }
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
            for (value, bytes) in payload.chunks_exact(32).enumerate() {
                let x = WideExact::from_le_bytes(bytes).ok_or(Error::NonCanonical { row, value })?;
                if x.c1() != QM31::ZERO { return Err(Error::NonCanonical { row, value }); }
            }
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
            out[value] =
                WideExact::from_le_bytes(bytes).ok_or(Error::NonCanonical { row, value })?;
        }
        Ok(out)
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

        fn sample_block(&mut self, row: u8, framed: &[u8]) -> Result<[u8; 32], Error> {
            if row != self.next_row {
                return Err(Error::RowOrder {
                    expected: self.next_row,
                    actual: row,
                });
            }
            parse_record(row, framed)?;
            // Exactly one absorb, one squeeze and one advance. Both reads
            // use s_abs; advancing from the challenge block would be wrong.
            let absorbed = (self.hash)(&[&self.state, &[0, 0xa0 + row], framed]);
            let block = (self.hash)(&[&absorbed, &[1]]);
            self.state = (self.hash)(&[&absorbed, &[2]]);
            self.next_row += 1;
            Ok(block)
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
            parse_record(row, self.record(row)?)
        }
        /// Same row-25 decoder, with direct initialization of heap storage.
        pub fn point_claims_boxed(&self) -> Result<alloc::boxed::Box<PointClaims>, Error> {
            let payload=self.payload(25)?;
            if payload.len()!=32*CLAIMS {return Err(Error::Length{row:25});}
            let mut out=aspis_core::r0::heap::uninit::<PointClaims>().map_err(|_|Error::Allocation)?;
            unsafe {
                let p=out.as_mut_ptr().cast::<WideExact>();
                for j in 0..CLAIMS {
                    p.add(j).write(WideExact::from_le_bytes(&payload[j*32..(j+1)*32]).ok_or(Error::NonCanonical{row:25,value:j})?);
                }
                Ok(out.assume_init())
            }
        }
        pub fn point_claims(&self) -> Result<PointClaims, Error> {
            let flat = decode_values::<CLAIMS>(25, self.payload(25)?)?;
            Ok(core::array::from_fn(|point| {
                core::array::from_fn(|lane| flat[point * LANES + lane])
            }))
        }
    }

    /// MSB-first semantic coordinates; reverse these for R-D's eqWeight.
    pub fn statement_points(alpha: &[QM31; 10]) -> [[QM31; 10]; 3] {
        aspis_core::state_only_prefix::r0::statement_points(alpha)
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct Challenges {
        pub lambda: QM31,
        pub chi: QM31,
        pub theta: QM31,
        pub zc: [QM31; 10],
        pub mu: QM31,
        pub eta: QM31,
    }
    impl Challenges {
        /// R-D's SemanticBoundary challenge history, in model row order.
        pub fn with_alphas(&self, alpha: &[QM31; 10]) -> [WideExact; 25] {
            core::array::from_fn(|row| {
                WideExact::from_qm31(match row {
                    0 => self.lambda,
                    1 => self.chi,
                    2 => self.theta,
                    3..=12 => self.zc[row - 3],
                    13 => self.mu,
                    14 => self.eta,
                    _ => alpha[row - 15],
                })
            })
        }
    }
    /// Rows 0..14. Roots are the only commitment records; there is no helper
    /// zero-sum/registry absorb between row 2 and theta.
    pub fn begin(
        prefix: &Prefix<'_>,
        transcript: &mut SemanticTranscript,
    ) -> Result<Challenges, Error> {
        let lambda = transcript.semantic(0, prefix.record(0)?)?;
        let chi = transcript.semantic(1, prefix.record(1)?)?;
        let theta = transcript.semantic(2, prefix.record(2)?)?;
        let mut zc = [QM31::ZERO; 10];
        for (i, value) in zc.iter_mut().enumerate() {
            *value = transcript.semantic(3 + i as u8, prefix.record(3 + i as u8)?)?;
        }
        let mu = transcript.semantic(13, prefix.record(13)?)?;
        let eta = transcript.semantic(14, prefix.record(14)?)?;
        Ok(Challenges {
            lambda,
            chi,
            theta,
            zc,
            mu,
            eta,
        })
    }
