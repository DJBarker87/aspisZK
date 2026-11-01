#![feature(prelude_import)]
//! UNPROVED R1 COST PROBE. P2 only; no production entrypoint.
#![no_std]
extern crate core;
#[prelude_import]
use core::prelude::rust_2021::*;
extern crate alloc;
pub mod sampler {



    // Adopted R1 proof format (PREREG-PROOF-SIZE-2, 2026-10-19): compact QM31
    // storage and binary multiproofs. UNPROVED: see PROOF-SIZE-OBLIGATIONS.




    // Fixed public-shape scheduling for the host CT adoption candidate.









    //! UNPROVED COST PROBE. Byte-equivalence experiment for the R0 K sampler.
    use aspis_core::circle::{
        secure_ood_circle_point_from_parameter, SecureCirclePoint,
    };
    use aspis_core::field::{WideExact, CM31, M31, P, QM31};
    pub use aspis_core::r0_transcript::CircleRow;
    /// Divide a little-endian word array by P, retaining every quotient word.
    /// Dividends are below P * 2^32, so every division fits in u64.
    fn qm31_div_pass(mut rank: [u32; 8]) -> ([u32; 8], u32) {
        let mut remainder = 0u64;
        let mut j = 8usize;
        while j > 0 {
            j -= 1;
            let dividend = (remainder << 32) | u64::from(rank[j]);
            rank[j] = (dividend / u64::from(P)) as u32;
            remainder = dividend % u64::from(P);
        }
        (rank, remainder as u32)
    }
    /// The low four base-P digits already represent rank modulo P^4.
    fn qm31_digits(block: &[u8; 32]) -> [u32; 4] {
        let mut rank = [0u32; 8];
        let mut i = 0usize;
        while i < 8 {
            let start = 4 * i;
            rank[i] =
                u32::from_le_bytes([block[start], block[start + 1],
                            block[start + 2], block[start + 3]]);
            i += 1;
        }
        let mut digits = [0u32; 4];
        let mut i = 0usize;
        while i < 4 {
            let (quotient, digit) = qm31_div_pass(rank);
            rank = quotient;
            digits[i] = digit;
            i += 1;
        }
        digits
    }
    pub fn qm31_sample(block: &[u8; 32]) -> QM31 {
        let digits = qm31_digits(block);
        QM31 {
            c0: CM31::new(M31(digits[0]), M31(digits[1])),
            c1: CM31::new(M31(digits[2]), M31(digits[3])),
        }
    }
    /// Return the low eight base-P digits of the 256-bit little-endian block and
    /// the remaining quotient. This uses eight long divisions by P rather than
    /// first reducing the full block with 256 binary steps.
    fn low_base_p_digits(block: &[u8; 32]) -> ([u32; 8], u32) {
        let mut quotient: [u32; 8] =
            core::array::from_fn(|i|
                    u32::from_le_bytes(block[4 *
                                            i..4 * i + 4].try_into().unwrap()));
        let digits =
            core::array::from_fn(|_|
                    {
                        let mut remainder = 0u64;
                        for limb in quotient.iter_mut().rev() {
                            let dividend = (remainder << 32) | u64::from(*limb);
                            *limb = (dividend / u64::from(P)) as u32;
                            remainder = dividend % u64::from(P);
                        }
                        remainder as u32
                    });
        if false {
            if !quotient[1..].iter().all(|&limb| limb == 0) {
                ::core::panicking::panic("assertion failed: quotient[1..].iter().all(|&limb| limb == 0)")
            };
        };
        if false {
            if !(quotient[0] <= 256) {
                ::core::panicking::panic("assertion failed: quotient[0] <= 256")
            };
        };
        (digits, quotient[0])
    }
    fn decode8(digits: [u32; 8]) -> WideExact {
        WideExact::new(QM31 {
                c0: CM31::new(M31(digits[0]), M31(digits[1])),
                c1: CM31::new(M31(digits[2]), M31(digits[3])),
            },
            QM31 {
                c0: CM31::new(M31(digits[4]), M31(digits[5])),
                c1: CM31::new(M31(digits[6]), M31(digits[7])),
            })
    }
    /// Add a small integer to a base-P digit vector. Returns the carry beyond
    /// the final digit, which is at most one for the values used by the sampler.
    fn add_small_base_p(digits: &mut [u32; 8], mut addend: u32) -> bool {
        for digit in digits {
            let sum = u64::from(*digit) + u64::from(addend);
            *digit = (sum % u64::from(P)) as u32;
            addend = (sum / u64::from(P)) as u32;
        }
        if false {
            if !(addend <= 1) {
                ::core::panicking::panic("assertion failed: addend <= 1")
            };
        };
        addend != 0
    }
    /// `decode8(rank(block) mod P^8)`, byte-for-byte equivalent to the frozen
    /// R0 sampler. The repeated divisions directly produce the low eight digits.
    pub fn ordinary_sample(block: &[u8; 32]) -> WideExact {
        let (digits, _) = low_base_p_digits(block);
        decode8(digits)
    }
    /// `decode8((rank(block) mod (P^8 - 1)) + 1)`, byte-for-byte equivalent to
    /// the frozen R0 sampler. Since `P^8 ≡ 1 (mod P^8 - 1)`, the high quotient can
    /// be added to the low digits before the final increment. A carry past digit
    /// seven contributes one more modulo `P^8 - 1`.
    pub fn gamma_sample(block: &[u8; 32]) -> WideExact {
        let (mut digits, quotient) = low_base_p_digits(block);
        let wrapped = add_small_base_p(&mut digits, quotient + 1);
        if wrapped {
            let wrapped_again = add_small_base_p(&mut digits, 1);
            if false {
                if !!wrapped_again {
                    ::core::panicking::panic("assertion failed: !wrapped_again")
                };
            };
        }
        decode8(digits)
    }
    pub fn circle_sample(block: &[u8; 32], row: CircleRow)
        -> SecureCirclePoint {
        secure_ood_circle_point_from_parameter(qm31_sample(block)).unwrap_or_else(|_|
                {
                    aspis_core::transcript::circle_fallback_point(match row {
                            CircleRow::First => 0,
                            CircleRow::Second => 1,
                        })
                })
    }
}
pub mod semantic_wire {
    //! UNPROVED COST PROBE. Isolated S4 wire/transcript copy; K-only parse.
    use aspis_core::circle::SecureCirclePoint;
    use aspis_core::field::{WideExact, QM31};
    use crate::sampler::{circle_sample, qm31_sample, CircleRow};
    use aspis_core::transcript::HashFn;
    use alloc::vec::Vec;
    pub const DOMAIN: &[u8] = b"UNPROVED:R1:PRIVATE-SALTED:SEMANTIC:P3";
    pub const LANES: usize = 29;
    pub const POINTS: usize = 3;
    pub const CLAIMS: usize = POINTS * LANES;
    pub const C1_LANES: [usize; 27] =
        [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
                20, 21, 22, 23, 24, 25, 28];
    pub const C2_LANES: [usize; 2] = [26, 27];
    pub type PointClaims = [[WideExact; LANES]; POINTS];
    pub enum Error {
        Allocation,
        RowOrder {
            expected: u8,
            actual: u8,
        },
        InvalidRow,
        Tag {
            row: u8,
        },
        Length {
            row: u8,
        },
        NonCanonical {
            row: u8,
            value: usize,
        },
        Boundary {
            round: usize,
        },
        Terminal,
        EqualCirclePoints,
        TrailingBytes,
        Public,
    }
    #[automatically_derived]
    #[doc(hidden)]
    unsafe impl ::core::clone::TrivialClone for Error { }
    #[automatically_derived]
    impl ::core::clone::Clone for Error {
        #[inline]
        fn clone(&self) -> Error {
            let _: ::core::clone::AssertParamIsClone<u8>;
            let _: ::core::clone::AssertParamIsClone<usize>;
            *self
        }
    }
    #[automatically_derived]
    impl ::core::marker::Copy for Error { }
    #[automatically_derived]
    impl ::core::fmt::Debug for Error {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            match self {
                Error::Allocation =>
                    ::core::fmt::Formatter::write_str(f, "Allocation"),
                Error::RowOrder { expected: __self_0, actual: __self_1 } =>
                    ::core::fmt::Formatter::debug_struct_field2_finish(f,
                        "RowOrder", "expected", __self_0, "actual", &__self_1),
                Error::InvalidRow =>
                    ::core::fmt::Formatter::write_str(f, "InvalidRow"),
                Error::Tag { row: __self_0 } =>
                    ::core::fmt::Formatter::debug_struct_field1_finish(f, "Tag",
                        "row", &__self_0),
                Error::Length { row: __self_0 } =>
                    ::core::fmt::Formatter::debug_struct_field1_finish(f,
                        "Length", "row", &__self_0),
                Error::NonCanonical { row: __self_0, value: __self_1 } =>
                    ::core::fmt::Formatter::debug_struct_field2_finish(f,
                        "NonCanonical", "row", __self_0, "value", &__self_1),
                Error::Boundary { round: __self_0 } =>
                    ::core::fmt::Formatter::debug_struct_field1_finish(f,
                        "Boundary", "round", &__self_0),
                Error::Terminal =>
                    ::core::fmt::Formatter::write_str(f, "Terminal"),
                Error::EqualCirclePoints =>
                    ::core::fmt::Formatter::write_str(f, "EqualCirclePoints"),
                Error::TrailingBytes =>
                    ::core::fmt::Formatter::write_str(f, "TrailingBytes"),
                Error::Public =>
                    ::core::fmt::Formatter::write_str(f, "Public"),
            }
        }
    }
    #[automatically_derived]
    impl ::core::marker::StructuralPartialEq for Error { }
    #[automatically_derived]
    impl ::core::cmp::PartialEq for Error {
        #[inline]
        fn eq(&self, other: &Error) -> bool {
            let __self_discr = ::core::intrinsics::discriminant_value(self);
            let __arg1_discr = ::core::intrinsics::discriminant_value(other);
            __self_discr == __arg1_discr &&
                match (self, other) {
                    (Error::RowOrder { expected: __self_0, actual: __self_1 },
                        Error::RowOrder { expected: __arg1_0, actual: __arg1_1 }) =>
                        __self_0 == __arg1_0 && __self_1 == __arg1_1,
                    (Error::Tag { row: __self_0 }, Error::Tag { row: __arg1_0 })
                        => __self_0 == __arg1_0,
                    (Error::Length { row: __self_0 }, Error::Length {
                        row: __arg1_0 }) => __self_0 == __arg1_0,
                    (Error::NonCanonical { row: __self_0, value: __self_1 },
                        Error::NonCanonical { row: __arg1_0, value: __arg1_1 }) =>
                        __self_0 == __arg1_0 && __self_1 == __arg1_1,
                    (Error::Boundary { round: __self_0 }, Error::Boundary {
                        round: __arg1_0 }) => __self_0 == __arg1_0,
                    _ => true,
                }
        }
    }
    #[automatically_derived]
    impl ::core::cmp::Eq for Error {
        #[inline]
        #[doc(hidden)]
        #[coverage(off)]
        fn assert_fields_are_eq(&self) {
            let _: ::core::cmp::AssertParamIsEq<u8>;
            let _: ::core::cmp::AssertParamIsEq<usize>;
        }
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
        if record.len() != 5 + size { return Err(Error::Length { row }); }
        if record[0] != tag { return Err(Error::Tag { row }); }
        if u32::from_le_bytes(record[1..5].try_into().unwrap()) as usize !=
                size {
            return Err(Error::Length { row });
        }
        let payload = &record[5..];
        if row >= 14 {
            for (value, bytes) in payload.chunks_exact(32).enumerate() {
                let x =
                    WideExact::from_le_bytes(bytes).ok_or(Error::NonCanonical {
                                row,
                                value,
                            })?;
                if x.c1() != QM31::ZERO {
                    return Err(Error::NonCanonical { row, value });
                }
            }
        }
        Ok(payload)
    }
    pub fn record(row: u8, payload: &[u8]) -> Result<Vec<u8>, Error> {
        let (tag, size) = row_shape(row).ok_or(Error::InvalidRow)?;
        if payload.len() != size { return Err(Error::Length { row }); }
        let mut out = Vec::with_capacity(5 + size);
        out.push(tag);
        out.extend_from_slice(&(size as u32).to_le_bytes());
        out.extend_from_slice(payload);
        parse_record(row, &out)?;
        Ok(out)
    }
    pub fn encode_values(values: impl IntoIterator<Item = WideExact>)
        -> Vec<u8> {
        let mut out = Vec::new();
        for value in values { out.extend_from_slice(&value.to_le_bytes()); }
        out
    }
    pub fn decode_values<const N : usize>(row: u8, payload: &[u8])
        -> Result<[WideExact; N], Error> {
        if payload.len() != 32 * N { return Err(Error::Length { row }); }
        let mut out = [WideExact::ZERO; N];
        for (value, bytes) in payload.chunks_exact(32).enumerate() {
            out[value] =
                WideExact::from_le_bytes(bytes).ok_or(Error::NonCanonical {
                            row,
                            value,
                        })?;
        }
        Ok(out)
    }
    /// Fresh R0 state, separate from Transcript's legacy all-zero IV. The
    /// C1-time binding is exactly SPEC §9: public bytes and the C1 root in one
    /// hash, with no profile/basis/nonce/registry pre-absorbs. Row 0 is empty.
    pub struct SemanticTranscript {
        state: [u8; 32],
        hash: HashFn,
        next_row: u8,
    }
    #[automatically_derived]
    impl ::core::clone::Clone for SemanticTranscript {
        #[inline]
        fn clone(&self) -> SemanticTranscript {
            SemanticTranscript {
                state: ::core::clone::Clone::clone(&self.state),
                hash: ::core::clone::Clone::clone(&self.hash),
                next_row: ::core::clone::Clone::clone(&self.next_row),
            }
        }
    }
    impl SemanticTranscript {
        pub fn new(hash: HashFn, public_bytes: &[u8], c1_root: &[u8; 32])
            -> Result<Self, Error> {
            let length =
                u32::try_from(public_bytes.len()).map_err(|_| Error::Public)?;
            Ok(Self {
                    state: hash(&[DOMAIN, &[0], &length.to_le_bytes(),
                                    public_bytes, c1_root]),
                    hash,
                    next_row: 0,
                })
        }
        pub fn state(&self) -> [u8; 32] { self.state }
        pub fn next_row(&self) -> u8 { self.next_row }
        fn sample_block(&mut self, row: u8, framed: &[u8])
            -> Result<[u8; 32], Error> {
            if row != self.next_row {
                return Err(Error::RowOrder {
                            expected: self.next_row,
                            actual: row,
                        });
            }
            parse_record(row, framed)?;
            let absorbed =
                (self.hash)(&[&self.state, &[0, 0xa0 + row], framed]);
            let block = (self.hash)(&[&absorbed, &[1]]);
            self.state = (self.hash)(&[&absorbed, &[2]]);
            self.next_row += 1;
            Ok(block)
        }
        pub fn semantic(&mut self, row: u8, framed: &[u8])
            -> Result<QM31, Error> {
            if row > 24 { return Err(Error::InvalidRow); }
            Ok(qm31_sample(&self.sample_block(row, framed)?))
        }
        /// R-B's one-block reference-circle map, including fixed fallback.
        /// The legacy Transcript method has a different parameter sampler.
        pub fn challenge_reference_circle_point(&mut self, row: u8,
            framed: &[u8]) -> Result<SecureCirclePoint, Error> {
            let circle_row =
                match row {
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
            if bytes.len() < 32 { return Err(Error::Length { row: 0 }); }
            let c1_root = bytes[..32].try_into().unwrap();
            let mut records = [&[][..]; 27];
            let mut offset = 32;
            for row in 0..27u8 {
                let length = 5 + row_shape(row).unwrap().1;
                let framed =
                    bytes.get(offset..offset +
                                        length).ok_or(Error::Length { row })?;
                parse_record(row, framed)?;
                records[row as usize] = framed;
                offset += length;
            }
            if offset != bytes.len() { return Err(Error::TrailingBytes); }
            Ok(Self { c1_root, records })
        }
        pub fn record(&self, row: u8) -> Result<&'a [u8], Error> {
            self.records.get(row as usize).copied().ok_or(Error::InvalidRow)
        }
        pub fn payload(&self, row: u8) -> Result<&'a [u8], Error> {
            parse_record(row, self.record(row)?)
        }
        /// Same row-25 decoder, with direct initialization of heap storage.
        pub fn point_claims_boxed(&self)
            -> Result<alloc::boxed::Box<PointClaims>, Error> {
            let payload = self.payload(25)?;
            if payload.len() != 32 * CLAIMS {
                return Err(Error::Length { row: 25 });
            }
            let mut out =
                aspis_core::r0::heap::uninit::<PointClaims>().map_err(|_|
                            Error::Allocation)?;
            unsafe {
                let p = out.as_mut_ptr().cast::<WideExact>();
                for j in 0..CLAIMS {
                    p.add(j).write(WideExact::from_le_bytes(&payload[j *
                                                    32..(j + 1) *
                                                    32]).ok_or(Error::NonCanonical { row: 25, value: j })?);
                }
                Ok(out.assume_init())
            }
        }
        pub fn point_claims(&self) -> Result<PointClaims, Error> {
            let flat = decode_values::<CLAIMS>(25, self.payload(25)?)?;
            Ok(core::array::from_fn(|point|
                        {
                            core::array::from_fn(|lane| flat[point * LANES + lane])
                        }))
        }
    }
    /// MSB-first semantic coordinates; reverse these for R-D's eqWeight.
    pub fn statement_points(alpha: &[QM31; 10]) -> [[QM31; 10]; 3] {
        aspis_core::state_only_prefix::r0::statement_points(alpha)
    }
    pub struct Challenges {
        pub lambda: QM31,
        pub chi: QM31,
        pub theta: QM31,
        pub zc: [QM31; 10],
        pub mu: QM31,
        pub eta: QM31,
    }
    #[automatically_derived]
    #[doc(hidden)]
    unsafe impl ::core::clone::TrivialClone for Challenges { }
    #[automatically_derived]
    impl ::core::clone::Clone for Challenges {
        #[inline]
        fn clone(&self) -> Challenges {
            let _: ::core::clone::AssertParamIsClone<QM31>;
            let _: ::core::clone::AssertParamIsClone<[QM31; 10]>;
            *self
        }
    }
    #[automatically_derived]
    impl ::core::marker::Copy for Challenges { }
    #[automatically_derived]
    impl ::core::fmt::Debug for Challenges {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            let names: &'static _ =
                &["lambda", "chi", "theta", "zc", "mu", "eta"];
            let values: &[&dyn ::core::fmt::Debug] =
                &[&self.lambda, &self.chi, &self.theta, &self.zc, &self.mu,
                            &&self.eta];
            ::core::fmt::Formatter::debug_struct_fields_finish(f,
                "Challenges", names, values)
        }
    }
    #[automatically_derived]
    impl ::core::marker::StructuralPartialEq for Challenges { }
    #[automatically_derived]
    impl ::core::cmp::PartialEq for Challenges {
        #[inline]
        fn eq(&self, other: &Challenges) -> bool {
            self.lambda == other.lambda && self.chi == other.chi &&
                            self.theta == other.theta && self.zc == other.zc &&
                    self.mu == other.mu && self.eta == other.eta
        }
    }
    #[automatically_derived]
    impl ::core::cmp::Eq for Challenges {
        #[inline]
        #[doc(hidden)]
        #[coverage(off)]
        fn assert_fields_are_eq(&self) {
            let _: ::core::cmp::AssertParamIsEq<QM31>;
            let _: ::core::cmp::AssertParamIsEq<[QM31; 10]>;
        }
    }
    impl Challenges {
        /// R-D's SemanticBoundary challenge history, in model row order.
        pub fn with_alphas(&self, alpha: &[QM31; 10]) -> [WideExact; 25] {
            core::array::from_fn(|row|
                    {
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
    pub fn begin(prefix: &Prefix<'_>, transcript: &mut SemanticTranscript)
        -> Result<Challenges, Error> {
        let lambda = transcript.semantic(0, prefix.record(0)?)?;
        let chi = transcript.semantic(1, prefix.record(1)?)?;
        let theta = transcript.semantic(2, prefix.record(2)?)?;
        let mut zc = [QM31::ZERO; 10];
        for (i, value) in zc.iter_mut().enumerate() {
            *value =
                transcript.semantic(3 + i as u8,
                        prefix.record(3 + i as u8)?)?;
        }
        let mu = transcript.semantic(13, prefix.record(13)?)?;
        let eta = transcript.semantic(14, prefix.record(14)?)?;
        Ok(Challenges { lambda, chi, theta, zc, mu, eta })
    }
}
pub mod semantic {
    //! UNPROVED COST PROBE. S4 semantic equations evaluated in K.
    use alloc::boxed::Box;
    use aspis_core::{circle::SecureCirclePoint, field::QM31, HashFn};
    use aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public;
    use crate::semantic_wire::{
        self as wire, Challenges, Error, Prefix, SemanticTranscript,
    };
    pub struct Verified {
        pub roots: [[u8; 32]; 2],
        pub challenges: Challenges,
        pub alpha: [QM31; 10],
        pub claims: Box<[[QM31; 29]; 3]>,
        pub before_z1: [QM31; 29],
        pub state_before_z0: [u8; 32],
        pub z: [SecureCirclePoint; 2],
        pub transcript: SemanticTranscript,
        pub round_checks: [[QM31; 3]; 10],
        pub terminal: QM31,
        pub masked_terminal: QM31,
    }
    pub fn decode<const N : usize>(row: u8, bytes: &[u8])
        -> Result<[QM31; N], Error> {
        if bytes.len() != N * 32 { return Err(Error::Length { row }); }
        let mut out = [QM31::ZERO; N];
        for (value, part) in bytes.chunks_exact(32).enumerate() {
            if part[16..].iter().any(|&b| b != 0) {
                return Err(Error::NonCanonical { row, value });
            }
            out[value] =
                QM31::from_le_bytes(&part[..16]).ok_or(Error::NonCanonical {
                            row,
                            value,
                        })?;
        }
        Ok(out)
    }
    #[inline(never)]
    fn claims(prefix: &Prefix<'_>) -> Result<Box<[[QM31; 29]; 3]>, Error> {
        let bytes = prefix.payload(25)?;
        let mut out =
            aspis_core::r0::heap::uninit::<[[QM31; 29]; 3]>().map_err(|_|
                        Error::Allocation)?;
        unsafe {
            for p in 0..3 {
                out.as_mut_ptr().cast::<[QM31; 29]>().add(p).write(decode::<29>(25,
                            &bytes[p * 29 * 32..(p + 1) * 29 * 32])?);
            }
            Ok(out.assume_init())
        }
    }
    #[inline(never)]
    pub fn verify(public: Public<'_>, bytes: &[u8], hash: HashFn)
        -> Result<Verified, Error> {
        let prefix = Prefix::parse(bytes)?;
        let mut transcript =
            SemanticTranscript::new(hash,
                    &public.public_bytes().map_err(|_| Error::Public)?,
                    prefix.c1_root)?;
        let challenges = wire::begin(&prefix, &mut transcript)?;
        let mut running = decode::<1>(14, prefix.payload(14)?)?[0];
        let mut alpha = [QM31::ZERO; 10];
        let mut round_checks = [[QM31::ZERO; 3]; 10];
        for round in 0..10 {
            let row = 15 + round as u8;
            let polynomial = decode::<28>(row, prefix.payload(row)?)?;
            let boundary =
                polynomial.iter().copied().fold(polynomial[0], QM31::add);
            if boundary != running { return Err(Error::Boundary { round }); }
            alpha[round] = transcript.semantic(row, prefix.record(row)?)?;
            let value =
                polynomial.iter().rev().fold(QM31::ZERO,
                    |a, &c| a.mul(alpha[round]).add(c));
            round_checks[round] = [running, boundary, value];
            running = value;
        }
        let claims = claims(&prefix)?;
        let original_challenges =
            aspis_core::state_only_prefix::r0::Challenges {
                lambda: challenges.lambda,
                chi: challenges.chi,
                theta: challenges.theta,
                zc: challenges.zc,
                mu: challenges.mu,
                eta: challenges.eta,
            };
        let terminal =
            public.terminal_qm31(&claims, &alpha,
                        &original_challenges).map_err(|_| Error::Public)?;
        let mask =
            aspis_core::state_only_hiding::state_only_selected_mask_value(&core::array::from_fn(|i|
                            claims[0][i]), &core::array::from_fn(|i| claims[0][16 + i]),
                claims[0][27], &alpha);
        let masked_terminal = mask.add(challenges.eta.mul(terminal));
        if running != masked_terminal { return Err(Error::Terminal); }
        let state_before_z0 = transcript.state();
        let z0 =
            transcript.challenge_reference_circle_point(25,
                    prefix.record(25)?)?;
        let before_z1 = decode::<29>(26, prefix.payload(26)?)?;
        let z1 =
            transcript.challenge_reference_circle_point(26,
                    prefix.record(26)?)?;
        if z0 == z1 { return Err(Error::EqualCirclePoints); }
        Ok(Verified {
                roots: [*prefix.c1_root,
                        prefix.payload(2)?.try_into().unwrap()],
                challenges,
                alpha,
                claims,
                before_z1,
                state_before_z0,
                z: [z0, z1],
                transcript,
                round_checks,
                terminal,
                masked_terminal,
            })
    }
}
pub mod fast_domain {
    //! Exact, factored evaluation of the checked R0 fibre domain.
    //!
    //! For u = 512*hi + lo, reversing its 18 bits gives
    //! `rev18(u) = (reverse9(lo) << 9) + reverse9(hi)`. Therefore the specified
    //! point `g^(1024 + 4096*rev18(u))` is exactly the product of the A and B
    //! table entries below. These generated constants only replace exponentiation
    //! with two indexed loads and one CM31 multiplication; the domain, generator,
    //! index map, and protocol behavior are unchanged.
    use aspis_core::field::{CM31, M31};
    use aspis_core::r0::domain::{FibreIndex, Point};
    const TABLE_A: [(u32, u32); 512] =
        [(1022251061, 788094511), (788094511, 1125232586),
                (1462922215, 117240331), (117240331, 684561432),
                (479936188, 217587789), (217587789, 1667547459),
                (797223315, 1892184156), (1892184156, 1350260332),
                (1601663285, 2022005567), (2022005567, 545820362),
                (1715132412, 1963268365), (1963268365, 432351235),
                (1329069890, 1640136239), (1640136239, 818413757),
                (1052324090, 1064735370), (1064735370, 1095159557),
                (119109612, 1742172267), (1742172267, 2028374035),
                (1949036272, 2084561085), (2084561085, 198447375),
                (1276985988, 456990464), (456990464, 870497659),
                (818046810, 1849544479), (1849544479, 1329436837),
                (1068288753, 675427495), (675427495, 1079194894),
                (2144102382, 886761621), (886761621, 3381265),
                (1542630618, 1177056098), (1177056098, 604853029),
                (270443035, 1665395253), (1665395253, 1877040612),
                (1319895764, 573785706), (573785706, 827587883),
                (614428895, 566940551), (566940551, 1533054752),
                (1614159808, 1309336248), (1309336248, 533323839),
                (20753985, 1635511764), (1635511764, 2126729662),
                (1685341984, 359481912), (359481912, 462141663),
                (1152154081, 2106306808), (2106306808, 995329566),
                (638582271, 300788326), (300788326, 1508901376),
                (1412610045, 1446210525), (1446210525, 734873602),
                (1747362177, 1031300071), (1031300071, 400121470),
                (45393311, 1630721361), (1630721361, 2102090336),
                (628786761, 140902127), (140902127, 1518696886),
                (1117531616, 1012065003), (1012065003, 1029952031),
                (320524274, 1536842560), (1536842560, 1826959373),
                (362376885, 1168590975), (1168590975, 1785106762),
                (1108016105, 252024370), (252024370, 1039467542),
                (1225642256, 1294224634), (1294224634, 921841391),
                (400584953, 469433912), (469433912, 1746898694),
                (932754395, 1184859162), (1184859162, 1214729252),
                (1636215277, 965201017), (965201017, 511268370),
                (993237774, 289789953), (289789953, 1154245873),
                (1844375598, 1823771499), (1823771499, 303108049),
                (1036868259, 1302232773), (1302232773, 1110615388),
                (1489475671, 1590331411), (1590331411, 658007976),
                (271955858, 2011039234), (2011039234, 1875527789),
                (494932510, 292984488), (292984488, 1652551137),
                (1415786230, 1111815158), (1111815158, 731697417),
                (1150508049, 626837953), (626837953, 996975598),
                (317286896, 920117449), (920117449, 1830196751),
                (1935941148, 1205027416), (1205027416, 211542499),
                (809155383, 303944815), (303944815, 1338328264),
                (541880188, 1280134915), (1280134915, 1605603459),
                (1598024857, 1875094528), (1875094528, 549458790),
                (405858396, 413054922), (413054922, 1741625251),
                (1343434959, 1740046445), (1740046445, 804048688),
                (1697594322, 1318496168), (1318496168, 449889325),
                (1908257733, 904587623), (904587623, 239225914),
                (1569205000, 1460088186), (1460088186, 578278647),
                (742503567, 20511103), (20511103, 1404980080),
                (924436841, 179213100), (179213100, 1223046806),
                (776651208, 1692488596), (1692488596, 1370832439),
                (685109443, 308131929), (308131929, 1462374204),
                (1418607411, 1674242439), (1674242439, 728876236),
                (1831338762, 818744620), (818744620, 316144885),
                (136027637, 84984741), (84984741, 2011456010),
                (832857621, 1800803482), (1800803482, 1314626026),
                (1029184762, 1463990705), (1463990705, 1118298885),
                (1026246497, 462715637), (462715637, 1121237150),
                (1630230719, 432660073), (432660073, 517252928),
                (789199007, 265368403), (265368403, 1358284640),
                (905527003, 2103042246), (2103042246, 1241956644),
                (966963960, 791773240), (791773240, 1180519687),
                (429418708, 1721759118), (1721759118, 1718064939),
                (226919109, 591805476), (591805476, 1920564538),
                (1601482956, 1555011007), (1555011007, 546000691),
                (925678133, 1851895798), (1851895798, 1221805514),
                (890643854, 2061547316), (2061547316, 1256839793),
                (2045776109, 764411913), (764411913, 101707538),
                (142321536, 2005775263), (2005775263, 2005162111),
                (852511271, 383685221), (383685221, 1294972376),
                (1850100142, 606004238), (606004238, 297383505),
                (1988413837, 422428418), (422428418, 159069810),
                (1145573298, 2059018920), (2059018920, 1001910349),
                (1024200565, 2131726269), (2131726269, 1123283082),
                (1335475227, 1076118019), (1076118019, 812008420),
                (430897376, 660937846), (660937846, 1716586271),
                (178995476, 298519990), (298519990, 1968488171),
                (1413092576, 2009537990), (2009537990, 734391071),
                (424922113, 74654605), (74654605, 1722561534),
                (665291814, 184778403), (184778403, 1482191833),
                (90485419, 2034131803), (2034131803, 2056998228),
                (1608154088, 833338502), (833338502, 539329559),
                (473403782, 542036433), (542036433, 1674079865),
                (955512264, 573921543), (573921543, 1191971383),
                (661117737, 832530753), (832530753, 1486365910),
                (251387545, 585003076), (585003076, 1896096102),
                (661565914, 1221956578), (1221956578, 1485917733),
                (420922661, 1190171598), (1190171598, 1726560986),
                (746184711, 1733602777), (1733602777, 1401298936),
                (1717922210, 1653599957), (1653599957, 429561437),
                (742148341, 1117355050), (1117355050, 1405335306),
                (2123635407, 1081507110), (1081507110, 23848240),
                (1274756874, 824918498), (824918498, 872726773),
                (75612694, 638305945), (638305945, 2071870953),
                (1146595981, 37855626), (37855626, 1000887666),
                (1128749075, 1106851245), (1106851245, 1018734572),
                (1189119296, 1858928305), (1858928305, 958364351),
                (1936509027, 329657887), (329657887, 210974620),
                (2067891986, 853385273), (853385273, 79591661),
                (242763393, 80138650), (80138650, 1904720254),
                (202216255, 1166833230), (1166833230, 1945267392),
                (1704605091, 1002003657), (1002003657, 442878556),
                (1228317011, 328390175), (328390175, 919166636),
                (1870718732, 902417887), (902417887, 276764915),
                (1517692234, 1936279112), (1936279112, 629791413),
                (1050410086, 1073301032), (1073301032, 1097073561),
                (558333589, 618725725), (618725725, 1589150058),
                (188438465, 212575099), (212575099, 1959045182),
                (2107512806, 635240816), (635240816, 39970841),
                (1351399750, 1217896196), (1217896196, 796083897),
                (740661540, 1927215114), (1927215114, 1406822107),
                (558100220, 1980501108), (1980501108, 1589383427),
                (2109249359, 247223496), (247223496, 38234288),
                (1012525923, 71691935), (71691935, 1134957724),
                (1828798623, 27117548), (27117548, 318685024),
                (2039959946, 1457037680), (1457037680, 107523701),
                (2038288495, 670227777), (670227777, 109195152),
                (209663158, 168116384), (168116384, 1937820489),
                (984290948, 99941766), (99941766, 1163192699),
                (1252927563, 799345076), (799345076, 894556084),
                (419428947, 1890870518), (1890870518, 1728054700),
                (1157494553, 1817015079), (1817015079, 989989094),
                (891334987, 1040656207), (1040656207, 1256148660),
                (785785922, 1967683322), (1967683322, 1361697725),
                (1302242334, 693913202), (693913202, 845241313),
                (1932511129, 687696804), (687696804, 214972518),
                (429857837, 1376073165), (1376073165, 1717625810),
                (778346524, 2089805548), (2089805548, 1369137123),
                (1132767988, 594038315), (594038315, 1014715659),
                (2078867071, 276497442), (276497442, 68616576),
                (22088804, 47256722), (47256722, 2125394843),
                (2089806413, 155403522), (155403522, 57677234),
                (396887507, 760876211), (760876211, 1750596140),
                (1005915392, 1867478512), (1867478512, 1141568255),
                (1098427204, 880292698), (880292698, 1049056443),
                (10571466, 1530894063), (1530894063, 2136912181),
                (1927076832, 605215390), (605215390, 220406815),
                (1461025413, 1421466600), (1421466600, 686458234),
                (725035983, 816938404), (816938404, 1422447664),
                (381944357, 1303428041), (1303428041, 1765539290),
                (1593271412, 1557280492), (1557280492, 554212235),
                (2095613886, 527857063), (527857063, 51869761),
                (2125667422, 1995711117), (1995711117, 21816225),
                (1589276025, 1583924546), (1583924546, 558207622),
                (425606435, 736395182), (736395182, 1721877212),
                (820025422, 857904003), (857904003, 1327458225),
                (367584259, 2107277889), (2107277889, 1779899388),
                (1845204024, 116979180), (116979180, 302279623),
                (1158837492, 819566845), (819566845, 988646155),
                (1766982315, 596409291), (596409291, 380501332),
                (1060867294, 1016052282), (1016052282, 1086616353),
                (15470579, 1643565293), (1643565293, 2132013068),
                (1886413538, 1618829578), (1618829578, 261070109),
                (1399753701, 1692335411), (1692335411, 747729946),
                (1150072909, 950473072), (950473072, 997410738),
                (894752084, 1749876144), (1749876144, 1252731563),
                (1770167713, 338572024), (338572024, 377315934),
                (1674153723, 1322319557), (1322319557, 473329924),
                (1189130906, 937749255), (937749255, 958352741),
                (406765125, 1121751370), (1121751370, 1740718522),
                (667409179, 1770171037), (1770171037, 1480074468),
                (336549856, 2103544920), (2103544920, 1810933791),
                (1914474864, 440166738), (440166738, 233008783),
                (2003660710, 1164690642), (1164690642, 143822937),
                (440188121, 714460670), (714460670, 1707295526),
                (1894212231, 1899640059), (1899640059, 253271416),
                (1270997537, 1765408850), (1765408850, 876486110),
                (834173210, 2010056637), (2010056637, 1313310437),
                (1080830343, 1196541462), (1196541462, 1066653304),
                (703912353, 1783773358), (1783773358, 1443571294),
                (153621575, 797360221), (797360221, 1993862072),
                (635778846, 1298887220), (1298887220, 1511704801),
                (1420391248, 495658886), (495658886, 727092399),
                (1273099376, 2109025845), (2109025845, 874384271),
                (290670999, 484618707), (484618707, 1856812648),
                (1953093309, 1399852939), (1399852939, 194390338),
                (1931790297, 476503814), (476503814, 215693350),
                (1168611337, 1316554005), (1316554005, 978872310),
                (1318032416, 914753745), (914753745, 829451231),
                (1016770609, 602494260), (602494260, 1130713038),
                (45277316, 1384212302), (1384212302, 2102206331),
                (298013744, 1631477536), (1631477536, 1849469903),
                (1504211713, 91770747), (91770747, 643271934),
                (321646901, 781973549), (781973549, 1825836746),
                (1957773767, 58465136), (58465136, 189709880),
                (838659345, 1494392856), (1494392856, 1308824302),
                (1184172815, 1501800213), (1501800213, 963310832),
                (1421224217, 977701755), (977701755, 726259430),
                (1514835708, 825288080), (825288080, 632647939),
                (963110699, 493845922), (493845922, 1184372948),
                (845600471, 1262183431), (1262183431, 1301883176),
                (779436839, 223436892), (223436892, 1368046808),
                (1371651014, 244997852), (244997852, 775832633),
                (1368395169, 2122900869), (2122900869, 779088478),
                (2039730200, 1811033336), (1811033336, 107753447),
                (162657442, 1560528002), (1560528002, 1984826205),
                (1553098421, 1743803217), (1743803217, 594385226),
                (24486645, 110112918), (110112918, 2122997002),
                (1774553093, 1188070682), (1188070682, 372930554),
                (534092016, 1184883641), (1184883641, 1613391631),
                (1045751413, 627353290), (627353290, 1101732234),
                (903868214, 1028549284), (1028549284, 1243615433),
                (753759022, 1035405166), (1035405166, 1393724625),
                (1952803077, 464954162), (464954162, 194680570),
                (102502428, 487991121), (487991121, 2044981219),
                (286638124, 1789802823), (1789802823, 1860845523),
                (2092563395, 1015929240), (1015929240, 54920252),
                (324159263, 1533483219), (1533483219, 1823324384),
                (804875961, 1759135764), (1759135764, 1342607686),
                (706014569, 1757890570), (1757890570, 1441469078),
                (448402140, 760266418), (760266418, 1699081507),
                (375974868, 1233265083), (1233265083, 1771508779),
                (113762283, 452178713), (452178713, 2033721364),
                (931200852, 642566420), (642566420, 1216282795),
                (1681153485, 1692397259), (1692397259, 466330162),
                (285193818, 765163688), (765163688, 1862289829),
                (394346139, 1629953179), (1629953179, 1753137508),
                (1937755996, 1620967529), (1620967529, 209727651),
                (1742951453, 411462942), (411462942, 404532194),
                (300510473, 181714998), (181714998, 1846973174),
                (379559102, 697727211), (697727211, 1767924545),
                (1556533402, 2005793122), (2005793122, 590950245),
                (1694422100, 342104775), (342104775, 453061547),
                (512321057, 1271549173), (1271549173, 1635162590),
                (1502308947, 1936338240), (1936338240, 645174700),
                (1988815881, 645751943), (645751943, 158667766),
                (675847432, 1010741234), (1010741234, 1471636215),
                (501721213, 24836471), (24836471, 1645762434),
                (1358569314, 679273363), (679273363, 788914333),
                (1484722465, 1078988777), (1078988777, 662761182),
                (277190863, 2137253840), (2137253840, 1870292784),
                (816500702, 1764869715), (1764869715, 1330982945),
                (1259936220, 2067445894), (2067445894, 887547427),
                (1513273850, 1722220683), (1722220683, 634209797),
                (1564688601, 591957108), (591957108, 582795046),
                (1529521733, 1200601350), (1200601350, 617961914),
                (799417018, 157314149), (157314149, 1348066629),
                (1811854824, 734127761), (734127761, 335628823),
                (1312626624, 408174531), (408174531, 834857023),
                (388664435, 1700426073), (1700426073, 1758819212),
                (2129034372, 1920159279), (1920159279, 18449275),
                (1031337775, 1391460640), (1391460640, 1116145872),
                (2083000424, 83400055), (83400055, 64483223),
                (1755212887, 1545248590), (1545248590, 392270760),
                (97731769, 427520892), (427520892, 2049751878),
                (1461518819, 1258709018), (1258709018, 685964828),
                (822026787, 790328297), (790328297, 1325456860),
                (1887931203, 983768063), (983768063, 259552444),
                (1403104042, 1214106139), (1214106139, 744379605),
                (162197904, 1576977305), (1576977305, 1985285743),
                (1519708073, 1761924179), (1761924179, 627775574)];
    const TABLE_B: [(u32, u32); 512] =
        [(1, 0), (996212859, 1140996376), (2015554631, 1088093947),
                (816867225, 1001272228), (1420207432, 2023238517),
                (816861480, 962195439), (1720479643, 177413607),
                (451378731, 1322552846), (1330239767, 1446369578),
                (829529542, 1666749290), (1801405099, 774845311),
                (1643336673, 2137148295), (113986326, 1659849761),
                (754227675, 49211602), (1719877370, 1305056920),
                (124061924, 222841901), (1543902459, 1632329423),
                (1497033183, 266384758), (238192698, 21195821),
                (1718190259, 219728259), (837291277, 535367851),
                (28838794, 517661087), (1008640538, 1400738499),
                (18889267, 303036586), (1338697498, 1881711368),
                (1486319117, 1051308334), (57413392, 1672717428),
                (1698380290, 1660014787), (1128628559, 487113817),
                (1021297342, 1410478134), (36983955, 1951442989),
                (498386322, 1121034294), (1389168750, 838891026),
                (1636834739, 1597012617), (1454515876, 223346768),
                (1756352277, 1351837341), (240698073, 476721530),
                (427864406, 1584676261), (185070104, 2052638160),
                (1275605666, 2095784385), (296310565, 109983397),
                (72206514, 1289188236), (709836333, 1607887694),
                (1513780754, 2116268837), (472230981, 1127178204),
                (337258740, 799789868), (954563443, 1672118401),
                (1873486026, 204075296), (13191618, 303576968),
                (1514546700, 482975034), (1820378488, 1427649814),
                (20135698, 907128133), (1363572456, 1209117074),
                (1184836041, 810606909), (483972604, 51373831),
                (309323555, 1207665785), (1577483195, 846841358),
                (472215603, 885906123), (1804344690, 999799715),
                (175617284, 1795732353), (389608651, 1555639321),
                (594200728, 1849269846), (329547558, 1589038929),
                (2118815938, 2129511119), (438833264, 1327019128),
                (1247546638, 2100838754), (287625694, 714961257),
                (155805646, 741953977), (694768587, 1335510377),
                (414447487, 1660191568), (1684659278, 1370520300),
                (467042048, 2131513571), (1384581133, 347627210),
                (1780251437, 1948453877), (1421431969, 974095169),
                (961627178, 109177970), (1971845238, 153904061),
                (1188557366, 413281552), (1923810989, 1272366406),
                (2063888815, 129056561), (1635360495, 1075839836),
                (330063644, 208626297), (116111969, 557501350),
                (1516934575, 1368952111), (2128165408, 1866558246),
                (1794178592, 2103779454), (720638041, 1133563860),
                (1149377722, 1799983014), (1004021208, 1870425365),
                (706427304, 2023867009), (991418403, 1480232698),
                (1912203537, 1288850576), (1461783988, 258760706),
                (1321308009, 1742025967), (913493534, 2126309379),
                (1963867290, 360941673), (377761958, 572545120),
                (1665396419, 574316292), (373302001, 1507699234),
                (801595255, 1469213224), (2051626085, 490550043),
                (996029127, 950036227), (1288641239, 397886040),
                (1264385016, 642191549), (324121113, 147452506),
                (1953213394, 1643851743), (1002266725, 1988311862),
                (991463235, 37546859), (1174950059, 1819822737),
                (2040633711, 425180892), (213923363, 1047884791),
                (328526853, 975070234), (1825664712, 501661179),
                (656109024, 1300585869), (1145588529, 205357607),
                (2020371461, 1932572291), (1466126871, 410615561),
                (1161400406, 1079422807), (1209061891, 111843040),
                (952468088, 412399546), (640220223, 1154724018),
                (471738157, 668712505), (1791257284, 457765379),
                (317467001, 1766420009), (1581002989, 970103636),
                (632980202, 1582071541), (88625828, 522726826),
                (914753278, 1399904526), (1799120754, 343598868),
                (1039404017, 1538341569), (666420564, 2135132831),
                (1006212893, 1489058627), (844712212, 1454882131),
                (1438323515, 1182923843), (292417279, 377436135),
                (1952780205, 81555357), (521340221, 1824173925),
                (1485690416, 559378410), (1714778873, 1735902582),
                (1180311432, 639492535), (245650224, 1174726897),
                (25525334, 2000505072), (1606261854, 1606869623),
                (1061095678, 38145073), (124482577, 226221110),
                (172504864, 1916272282), (1564877543, 99597748),
                (876115079, 1775942790), (530115096, 90442098),
                (1392272834, 993120013), (399207028, 155898355),
                (1327578729, 1084731515), (607954189, 1091734815),
                (1323669817, 933421634), (1478673705, 1008068784),
                (1962335487, 1399131158), (1055871441, 345775465),
                (711647904, 1091839298), (881168337, 157473534),
                (1723511612, 1949091952), (263253631, 1948074535),
                (804296458, 213396278), (153716819, 2054656334),
                (2104095544, 1435777142), (1479292912, 403634516),
                (565878948, 1786880501), (682480399, 799350698),
                (1340472519, 1675598842), (735504938, 198004457),
                (848969192, 1414511411), (2083960347, 2126322313),
                (1209545065, 1852982367), (386684296, 1363813538),
                (1083568418, 725197280), (1439180125, 915904269),
                (1480502711, 1450760425), (1488671228, 939868393),
                (1982402, 431614399), (1542296538, 1163978019),
                (1244152270, 498961107), (1362074261, 2047718881),
                (563752921, 1285853654), (1834599352, 1895440138),
                (1662799443, 1810348412), (474711937, 1020011657),
                (1134947640, 394118266), (1739468984, 977169647),
                (227977990, 1816535211), (836848068, 529120781),
                (210740911, 1280364462), (581559614, 117257650),
                (510094092, 641201894), (503318431, 730224775),
                (1571876055, 1388714234), (1320977789, 1557620475),
                (118365627, 1759509849), (795729789, 119644040),
                (1386331726, 809207732), (753978456, 488132937),
                (662367932, 209372338), (940196297, 1361581394),
                (550623242, 753832155), (6376089, 129509954),
                (446322859, 1580452721), (1755458239, 1807540371),
                (2142868905, 574364801), (1596830861, 2049034655),
                (1180209648, 441139635), (338018326, 944583937),
                (1306248760, 633800785), (2075561284, 1405804402),
                (581907879, 73327176), (2049933380, 1834113202),
                (1783858788, 875557115), (1718311009, 1065402188),
                (1306014716, 1275597287), (1212070390, 338345678),
                (1460417120, 797602420), (1852933947, 203671172),
                (1545193553, 364584318), (1776630073, 603111274),
                (1049445738, 292144592), (954301220, 1901175687),
                (923367882, 1744922936), (347749121, 1576860820),
                (1986804722, 1373191730), (1616101075, 811514491),
                (147800194, 1069151092), (1565145988, 1765289675),
                (365445058, 1099441367), (920245660, 938576836),
                (204640856, 2040419027), (1213375404, 771547637),
                (2064624001, 245417806), (494233883, 1403803427),
                (1661270250, 1697085245), (818224288, 1972399941),
                (513998937, 202899553), (1757257503, 734249953),
                (1601634968, 1790370824), (1829052821, 673049321),
                (1765843037, 2085683345), (1213735332, 1357695652),
                (1332929929, 2095879383), (914918274, 1369105915),
                (1478304746, 406667278), (919065681, 1216872295),
                (1932017562, 1757637245), (44588143, 2058311453),
                (888152082, 1321895104), (1408222478, 1721187542),
                (210392081, 157752587), (1444319707, 1095294811),
                (1540140142, 751979754), (570004307, 1164891669),
                (1090698404, 2001864991), (595037635, 2111542451),
                (433157739, 937025459), (100684459, 1640456458),
                (1936161103, 1911011743), (2008329732, 1737289791),
                (748970643, 485565246), (1220431105, 100455014),
                (1661468032, 1401616134), (798338207, 2110850421),
                (1219048271, 773733831), (1789955189, 505997887),
                (321157045, 133308492), (1819903752, 1929668715),
                (354559414, 1412186133), (683528853, 193776762),
                (1371420477, 247094679), (1964662320, 1382435771),
                (1249682376, 474254021), (150937652, 383732090),
                (588173577, 946133187), (1250840269, 386418603),
                (122969455, 311337502), (332209582, 331411357),
                (2021756148, 85056840), (1631496031, 481893475),
                (964719250, 1012108343), (168460970, 1615303811),
                (1764389290, 1617898495), (422755315, 374503008),
                (1920015819, 2017323756), (719706205, 1755223690),
                (1871020210, 2067959207), (1421883301, 1767600112),
                (1742158212, 947474543), (848823435, 1634673682),
                (47282233, 1973840192), (1318914216, 1663922738),
                (500001204, 1350892375), (2079323762, 1208852267),
                (1386607805, 2069854787), (729011542, 952009042),
                (1995718635, 990602029), (1079208008, 2008108071),
                (985150678, 1044660427), (782570832, 476532960),
                (649844810, 475157379), (1462196868, 1013065725),
                (405825245, 2000126861), (606906923, 1264738384),
                (875583808, 1932435950), (1771477961, 772209956),
                (1153435498, 735309441), (291679777, 1578449442),
                (1036739736, 4090232), (1954195642, 800757595),
                (3045475, 162418948), (953139263, 265503960),
                (1255153497, 1873206092), (1109468214, 24685739),
                (1194288306, 1664016260), (1954241062, 1820169310),
                (461636029, 555407991), (878071934, 497955134),
                (1274127696, 398642911), (433600440, 167145119),
                (257107986, 1260243949), (2117360294, 299533990),
                (1968789303, 1889430098), (18918067, 521344418),
                (212412059, 1208547549), (526492512, 1146089824),
                (1854906262, 225292938), (2001642678, 1520422911),
                (1151864086, 1548621786), (1051514954, 1945490652),
                (1231259954, 511844620), (1936661821, 241049853),
                (54857805, 2021489568), (2138570352, 385731389),
                (830229400, 1396231886), (36975016, 821963373),
                (110720662, 731152038), (1672578949, 179250121),
                (1682843627, 18309514), (183117139, 65944434),
                (1584827345, 909175004), (1845239625, 562344050),
                (1315215493, 454778943), (1876139646, 119923533),
                (750500769, 1547263668), (849384769, 61803180),
                (1513012924, 2142060978), (174156438, 1448257952),
                (1976764966, 602953694), (1805314849, 466904232),
                (963560469, 803989913), (528497962, 2048433423),
                (668998651, 249239603), (58617043, 693726782),
                (1475204899, 1648029352), (1576856103, 1461690978),
                (1488450015, 601243945), (799756877, 308500462),
                (571821609, 1489087773), (1029245122, 1158447597),
                (1058730422, 1950344727), (1210158521, 1506582976),
                (826608058, 2050139532), (2076036242, 130048956),
                (185991083, 1518281638), (1797669071, 2141355836),
                (413934600, 1586830163), (845078094, 149898124),
                (674296139, 317324829), (25637092, 421692094),
                (970891652, 610465777), (647843950, 788293466),
                (148228362, 590602766), (69829270, 1352453515),
                (1683233817, 1287709593), (887385898, 608769478),
                (1269707845, 1452388824), (852276839, 226974950),
                (412577235, 1997534047), (1615674956, 1808914239),
                (406123904, 764760651), (2126452532, 708823575),
                (1991612315, 1875574124), (1475016787, 1876816901),
                (1065576003, 1260155159), (150344386, 103390841),
                (1736259183, 993645757), (458199028, 2319221),
                (870734736, 2085864614), (1388011311, 312501879),
                (1669933146, 467772885), (957870942, 905094216),
                (1326380755, 140779095), (1569000839, 48016228),
                (139466273, 1803083243), (1681738638, 1038838871),
                (1677449438, 113082240), (1490057922, 1016920220),
                (1801577965, 1312472321), (1214106985, 780900129),
                (1907575337, 569832496), (582949328, 603337063),
                (2009192190, 566186921), (236415000, 1220441885),
                (1100966113, 642444966), (2086832175, 647027993),
                (442183737, 184219552), (891287480, 1172290213),
                (398898618, 2000607785), (991079294, 1616314544),
                (641638338, 1769768123), (1085445012, 1626464664),
                (1917457045, 820650395), (1885905244, 1519283397),
                (2098046315, 239316783), (1984370174, 548484416),
                (1760363481, 2129820178), (1997990904, 355093967),
                (1980954341, 561676940), (207319829, 330698049),
                (480315830, 137067372), (1608197410, 953495473),
                (1433755461, 316564196), (591304555, 68989614),
                (569540672, 885330917), (865056590, 1396323689),
                (237150930, 715611246), (1167250594, 1854887903),
                (112696124, 268389163), (719959488, 88680757),
                (498135791, 1918711876), (854984042, 63484416),
                (512573355, 559650698), (450129036, 2130393939),
                (934129539, 1082077994), (787391422, 234435571),
                (808165703, 1317710352), (92769725, 1231653419),
                (1699669774, 817702196), (1696657789, 2121958423),
                (181669902, 1993442275), (1735177288, 1041858071),
                (265914936, 748543764), (2077839401, 709133143),
                (479770865, 2027287932), (1742529025, 278083478),
                (1334313253, 1249554241), (1124768046, 299494314),
                (1055409021, 1215994438), (333636023, 948573238),
                (548067276, 713948312), (1458581325, 1279621404),
                (1873772561, 1110881047), (994459063, 1883501554),
                (308028775, 1118600221), (1924483244, 1528988896),
                (176039723, 154417691), (841695573, 113926739),
                (52691895, 801280851), (1212320872, 1495300507),
                (540487422, 1063443989), (1994468584, 1611997849),
                (2119188567, 919124989), (1753543609, 1294275673),
                (1908790330, 386453773), (1573749961, 753946855),
                (305276529, 1041544704), (128738146, 457848703),
                (582395095, 1653762059), (1104635206, 858881536),
                (1504303166, 365743328), (122809504, 181977862),
                (617875881, 1291144021), (895013455, 284231781),
                (1880738855, 621634671), (1300871249, 1490001285),
                (454136966, 941654637), (277472845, 620479805),
                (594888648, 735387713), (1168068815, 1631133982),
                (598225672, 477392696), (1272345615, 2072662117),
                (1788571406, 979662875), (655623719, 353143806),
                (1258493728, 1482265298), (854296756, 1657148963),
                (1287455995, 1262269285), (1389630114, 73256692),
                (463066423, 383444756), (401706099, 967129345),
                (1055629173, 1510653447), (1775957340, 1042791219),
                (1767305484, 1767768510), (702523908, 198087577),
                (498379185, 365852161), (1029759507, 977441374),
                (531874659, 2093948690), (274337143, 1881376116),
                (1734948438, 924408729), (875099799, 1659345298),
                (1568619121, 824042977), (936298450, 1105042578),
                (1577684276, 2022021752), (404074859, 398369746),
                (931704942, 1582955093), (18011247, 565274326),
                (931164423, 2037669329), (1309629376, 2080668066),
                (1286492231, 1508399759), (1807661853, 544066780),
                (1942053500, 1814876063)];
    #[inline]
    fn table_value(value: (u32, u32)) -> CM31 {
        CM31::new(M31(value.0), M31(value.1))
    }
    /// Return exactly the core R0 fibre point for this checked index.
    #[inline]
    pub fn fibre_point(u: FibreIndex) -> Point<M31> {
        let index = u.get();
        let left = table_value(TABLE_A[index & 511]);
        let right = table_value(TABLE_B[index >> 9]);
        let point = left.mul(right);
        Point { x: point.a, y: point.b }
    }
    /// Return the R0 line node `2*x^2 - 1` for this checked fibre index.
    #[inline]
    pub fn line_node(u: FibreIndex) -> M31 {
        let x = fibre_point(u).x;
        let square = x.mul(x);
        square.double().sub(M31::ONE)
    }
}
pub mod fast_dots {
    //! Exact four-slot dot products with a partially reduced base-field prefix.
    use aspis_core::field::{M31, QM31, WideExact};
    use crate::fast_pairing::EbyKDot;
    /// Compute the verifier's four dot products while postponing canonical M31
    /// reductions across groups of at most four base-field products.
    ///
    /// Each limb product is at most `(P - 1)^2`; four products therefore sum to
    /// less than `2^64`, since `4 * (P - 1)^2 < 2^64`. One Mersenne fold
    /// `(sum & P) + (sum >> 31)` preserves its residue and is below `2^34`.
    /// Seven folded batches sum to less than `2^37`; canonicalize each limb once
    /// after all 26 products. Every byte decoder and its order are unchanged.
    fn four_dots_one(q: &[u8; 608], g: &[WideExact; 29], slot: usize)
        -> WideExact {
        let mut limbs = [0u64; WideExact::LIMB_COUNT];
        for start in (0..26).step_by(4) {
            let mut sums = [0u64; WideExact::LIMB_COUNT];
            for term in start..core::cmp::min(start + 4, 26) {
                let scalar =
                    M31::from_le_bytes(q[slot * 120 +
                                                term *
                                                    4..slot * 120 + term * 4 + 4].try_into().unwrap()).unwrap();
                let coefficient = g[term].to_limbs();
                sums[0] += u64::from(coefficient[0]) * u64::from(scalar.0);
                sums[1] += u64::from(coefficient[1]) * u64::from(scalar.0);
                sums[2] += u64::from(coefficient[2]) * u64::from(scalar.0);
                sums[3] += u64::from(coefficient[3]) * u64::from(scalar.0);
                sums[4] += u64::from(coefficient[4]) * u64::from(scalar.0);
                sums[5] += u64::from(coefficient[5]) * u64::from(scalar.0);
                sums[6] += u64::from(coefficient[6]) * u64::from(scalar.0);
                sums[7] += u64::from(coefficient[7]) * u64::from(scalar.0);
            }
            limbs[0] += (sums[0] & 0x7fff_ffff) + (sums[0] >> 31);
            limbs[1] += (sums[1] & 0x7fff_ffff) + (sums[1] >> 31);
            limbs[2] += (sums[2] & 0x7fff_ffff) + (sums[2] >> 31);
            limbs[3] += (sums[3] & 0x7fff_ffff) + (sums[3] >> 31);
            limbs[4] += (sums[4] & 0x7fff_ffff) + (sums[4] >> 31);
            limbs[5] += (sums[5] & 0x7fff_ffff) + (sums[5] >> 31);
            limbs[6] += (sums[6] & 0x7fff_ffff) + (sums[6] >> 31);
            limbs[7] += (sums[7] & 0x7fff_ffff) + (sums[7] >> 31);
        }
        let mut value =
            WideExact::from_limbs([M31::reduce_u64(limbs[0]).0,
                            M31::reduce_u64(limbs[1]).0, M31::reduce_u64(limbs[2]).0,
                            M31::reduce_u64(limbs[3]).0, M31::reduce_u64(limbs[4]).0,
                            M31::reduce_u64(limbs[5]).0, M31::reduce_u64(limbs[6]).0,
                            M31::reduce_u64(limbs[7]).0]).unwrap();
        let mut tail = EbyKDot::new();
        tail.push(g[28],
                QM31::from_le_bytes(&q[slot * 120 +
                                        104..slot * 120 + 120]).unwrap()).unwrap();
        let offset0 = 480 + slot * 32 + 0 * 16;
        tail.push(g[0 + 26],
                QM31::from_le_bytes(&q[offset0..offset0 +
                                        16]).unwrap()).unwrap();
        let offset1 = 480 + slot * 32 + 1 * 16;
        tail.push(g[1 + 26],
                QM31::from_le_bytes(&q[offset1..offset1 +
                                        16]).unwrap()).unwrap();
        value.add(tail.finish())
    }
    pub fn four_dots(q: &[u8], g: &[WideExact; 29]) -> [WideExact; 4] {
        let q: &[u8; 608] = q[..608].try_into().unwrap();
        [four_dots_one(q, g, 0), four_dots_one(q, g, 1),
                four_dots_one(q, g, 2), four_dots_one(q, g, 3)]
    }
}
pub mod fast_pairing {
    //! Exact-field dot accumulator candidates; arithmetic-only equivalence code.
    mod canonical {
        //! Private canonical representation: validate at the boundary, preserve internally.
        //! No public unchecked constructor. This does NOT change aspis_core::M31.
        pub const P: u32 = 0x7fff_ffff;
        const MASK: u64 = 0x7fff_ffff_7fff_ffff;
        const ONES: u64 = 0x0000_0001_0000_0001;
        pub struct Q([u32; 4]);
        #[automatically_derived]
        #[doc(hidden)]
        unsafe impl ::core::clone::TrivialClone for Q { }
        #[automatically_derived]
        impl ::core::clone::Clone for Q {
            #[inline]
            fn clone(&self) -> Q {
                let _: ::core::clone::AssertParamIsClone<[u32; 4]>;
                *self
            }
        }
        #[automatically_derived]
        impl ::core::marker::Copy for Q { }
        #[automatically_derived]
        impl ::core::fmt::Debug for Q {
            #[inline]
            fn fmt(&self, f: &mut ::core::fmt::Formatter)
                -> ::core::fmt::Result {
                ::core::fmt::Formatter::debug_tuple_field1_finish(f, "Q",
                    &&self.0)
            }
        }
        #[automatically_derived]
        impl ::core::marker::StructuralPartialEq for Q { }
        #[automatically_derived]
        impl ::core::cmp::PartialEq for Q {
            #[inline]
            fn eq(&self, other: &Q) -> bool { self.0 == other.0 }
        }
        #[automatically_derived]
        impl ::core::cmp::Eq for Q {
            #[inline]
            #[doc(hidden)]
            #[coverage(off)]
            fn assert_fields_are_eq(&self) {
                let _: ::core::cmp::AssertParamIsEq<[u32; 4]>;
            }
        }
        #[automatically_derived]
        impl ::core::default::Default for Q {
            #[inline]
            fn default() -> Q { Q(::core::default::Default::default()) }
        }
        #[inline(always)]
        pub(crate) fn reduce(mut x: u64) -> u32 {
            x = (x & u64::from(P)) + (x >> 31u32);
            x = (x & u64::from(P)) + (x >> 31u32);
            if x >= u64::from(P) {
                (x - u64::from(P)) as u32
            } else { x as u32 }
        }
        #[inline(always)]
        pub(crate) fn add(a: u32, b: u32) -> u32 {
            let s = a.wrapping_add(b);
            if s >= P { s - P } else { s }
        }
        #[inline(always)]
        fn pair(a: u32, b: u32) -> u64 { u64::from(a) | (u64::from(b) << 32) }
        #[inline(always)]
        fn reduce_pair(s: u64) -> u64 {
            (s.wrapping_add(((s.wrapping_add(ONES)) >> 31u32) & ONES)) & MASK
        }
        impl Q {
            pub const ZERO: Self = Self([0; 4]);
            pub const ONE: Self = Self([1, 0, 0, 0]);
            pub fn from_limbs(x: [u32; 4]) -> Option<Self> {
                let [a, b, c, d] = x;
                if a < P && b < P && c < P && d < P {
                    Some(Self([a, b, c, d]))
                } else { None }
            }
            pub fn from_m31(x: u32) -> Option<Self> {
                if x < P { Some(Self([x, 0, 0, 0])) } else { None }
            }
            pub const fn limbs(self) -> [u32; 4] { self.0 }
            /// WideExact owns private, canonical coordinates; this constructor
            /// accepts only that validated type, never raw QM31 limbs or bytes.
            #[inline(always)]
            pub(super) fn from_wide(value: super::E) -> [Self; 2] {
                let [a, b, c, d, e, f, g, h] = value.to_limbs();
                [Self([a, b, c, d]), Self([e, f, g, h])]
            }
            #[inline(always)]
            pub fn add(self, rhs: Self) -> Self {
                let a =
                    reduce_pair(pair(self.0[0],
                                self.0[1]).wrapping_add(pair(rhs.0[0], rhs.0[1])));
                let b =
                    reduce_pair(pair(self.0[2],
                                self.0[3]).wrapping_add(pair(rhs.0[2], rhs.0[3])));
                Self([a as u32, (a >> 32) as u32, b as u32, (b >> 32) as u32])
            }
            #[inline(always)]
            pub fn sub(self, rhs: Self) -> Self {
                let a =
                    reduce_pair(pair(self.0[0],
                                    self.0[1]).wrapping_add(MASK).wrapping_sub(pair(rhs.0[0],
                                rhs.0[1])));
                let b =
                    reduce_pair(pair(self.0[2],
                                    self.0[3]).wrapping_add(MASK).wrapping_sub(pair(rhs.0[2],
                                rhs.0[3])));
                Self([a as u32, (a >> 32) as u32, b as u32, (b >> 32) as u32])
            }
            #[inline(always)]
            pub fn half(self) -> Self {
                let h = |x: u32| (x >> 1) | ((x & 1) << 30);
                let mut out = [0u32; 4];
                for i in 0..4 { out[i] = h(self.0[i]); }
                Self(out)
            }
            pub fn half_pow(self, n: u8) -> Option<Self> {
                if n > 30 { return None }
                if n == 0 { return Some(self) }
                let mut out = [0u32; 4];
                for i in 0..4 {
                    let x = self.0[i];
                    out[i] = (x >> n) | ((x & ((1u32 << n) - 1)) << (31 - n));
                }
                Some(Self(out))
            }
            #[inline(always)]
            pub fn mul_m31(self, rhs: u32) -> Option<Self> {
                if rhs >= P { return None }
                let mut out = [0u32; 4];
                for i in 0..4 {
                    out[i] = reduce(u64::from(self.0[i]) * u64::from(rhs));
                }
                Some(Self(out))
            }
            /// Benchmark candidate, not an assertion of superiority over staged R19.
            /// All intermediates are nonnegative and strictly below 2^64.
            #[inline(always)]
            pub fn mul(self, rhs: Self) -> Self {
                let [a, b, c, d] =
                    [u64::from(self.0[0]), u64::from(self.0[1]),
                            u64::from(self.0[2]), u64::from(self.0[3])];
                let [e, f, g, h] =
                    [u64::from(rhs.0[0]), u64::from(rhs.0[1]),
                            u64::from(rhs.0[2]), u64::from(rhs.0[3])];
                const PP: u64 = (P as u64) * (P as u64);
                let partial =
                    |x: u64| (x & u64::from(P)).wrapping_add(x >> 31u32);
                let u = partial((c * g).wrapping_add(PP).wrapping_sub(d * h));
                let v = partial((c * h).wrapping_add(d * g));
                Self([reduce((a *
                                                            e).wrapping_add(PP).wrapping_sub(b *
                                                    f).wrapping_add(2 *
                                                u).wrapping_add(3 * u64::from(P)).wrapping_sub(v)),
                            reduce((a *
                                                    f).wrapping_add(b * e).wrapping_add(u).wrapping_add(2 * v)),
                            reduce((a *
                                                        g).wrapping_add(c *
                                                    e).wrapping_add(2 *
                                                PP).wrapping_sub(b * h).wrapping_sub(d * f)),
                            reduce((a *
                                                    h).wrapping_add(b *
                                                g).wrapping_add(c * f).wrapping_add(d * e))])
            }
        }
        impl Q {
            #[inline(always)]
            fn raw(self, rhs: Self) -> [u64; 4] {
                let [a, b, c, d] =
                    [u64::from(self.0[0]), u64::from(self.0[1]),
                            u64::from(self.0[2]), u64::from(self.0[3])];
                let [e, f, g, h] =
                    [u64::from(rhs.0[0]), u64::from(rhs.0[1]),
                            u64::from(rhs.0[2]), u64::from(rhs.0[3])];
                const PP: u64 = (P as u64) * (P as u64);
                let partial =
                    |x: u64| (x & u64::from(P)).wrapping_add(x >> 31u32);
                let u = partial((c * g).wrapping_add(PP).wrapping_sub(d * h));
                let v = partial((c * h).wrapping_add(d * g));
                [(a *
                                                    e).wrapping_add(PP).wrapping_sub(b *
                                            f).wrapping_add(2 *
                                        u).wrapping_add(3 * u64::from(P)).wrapping_sub(v),
                        (a *
                                            f).wrapping_add(b * e).wrapping_add(u).wrapping_add(2 * v),
                        (a *
                                                g).wrapping_add(c *
                                            e).wrapping_add(2 *
                                        PP).wrapping_sub(b * h).wrapping_sub(d * f),
                        (a *
                                            h).wrapping_add(b *
                                        g).wrapping_add(c * f).wrapping_add(d * e)]
            }
            #[inline(always)]
            pub fn dot<const N : usize>(left: [Self; N], right: [Self; N])
                -> Self {
                if !(N <= 4) {
                    ::core::panicking::panic("assertion failed: N <= 4")
                };
                let mut sums = [0u64; 4];
                for i in 0..N {
                    let raw = left[i].raw(right[i]);
                    for j in 0..4 {
                        sums[j] =
                            sums[j].wrapping_add((raw[j] &
                                            u64::from(P)).wrapping_add(raw[j] >> 31u32));
                    }
                }
                Self([reduce(sums[0]), reduce(sums[1]), reduce(sums[2]),
                            reduce(sums[3])])
            }
            #[inline(always)]
            pub fn neg(self) -> Self { Self::ZERO.sub(self) }
            #[inline(always)]
            pub fn square(self) -> Self { self.mul(self) }
        }
        pub struct Dot {
            sums: [u64; 4],
        }
        impl Dot {
            pub fn new() -> Self { Self { sums: [0; 4] } }
            #[inline(always)]
            pub fn push(&mut self, a: Q, b: Q) {
                let raw = a.raw(b);
                for j in 0..4 {
                    self.sums[j] =
                        self.sums[j].wrapping_add((raw[j] &
                                        u64::from(P)).wrapping_add(raw[j] >> 31u32));
                }
            }
            pub fn finish(self) -> Q {
                Q([reduce(self.sums[0]), reduce(self.sums[1]),
                            reduce(self.sums[2]), reduce(self.sums[3])])
            }
        }
    }
    use aspis_core::field::{CM31, QM31, WideExact as E};
    const MAX_TERMS: usize = 4096;
    #[inline(always)]
    fn limbs_of(k: QM31) -> [u32; 4] {
        [k.c0.a.0, k.c0.b.0, k.c1.a.0, k.c1.b.0]
    }
    #[inline(always)]
    fn checked_q(k: QM31) -> Result<canonical::Q, ()> {
        match canonical::Q::from_limbs(limbs_of(k)) {
            Some(q) => Ok(q),
            None => Err(()),
        }
    }
    #[inline(always)]
    fn qm31_of(q: canonical::Q) -> QM31 {
        let [a, b, c, d] = q.limbs();
        QM31 {
            c0: CM31 {
                a: aspis_core::field::M31(a),
                b: aspis_core::field::M31(b),
            },
            c1: CM31 {
                a: aspis_core::field::M31(c),
                b: aspis_core::field::M31(d),
            },
        }
    }
    /// Candidate exact accumulator for sums of `WideExact * QM31`.
    /// Canonical QM31 coordinates and the 4096-term limit are checked at push.
    pub struct EbyKDot {
        c0: canonical::Dot,
        c1: canonical::Dot,
        count: usize,
    }
    impl EbyKDot {
        pub fn new() -> Self {
            Self {
                c0: canonical::Dot::new(),
                c1: canonical::Dot::new(),
                count: 0,
            }
        }
        #[inline(always)]
        pub fn push(&mut self, value: E, scalar: QM31) -> Result<(), ()> {
            if self.count >= MAX_TERMS { return Err(()); }
            let [value_c0, value_c1] = canonical::Q::from_wide(value);
            let scalar = checked_q(scalar)?;
            self.c0.push(value_c0, scalar);
            self.c1.push(value_c1, scalar);
            self.count += 1;
            Ok(())
        }
        #[inline(always)]
        pub fn finish(self) -> E {
            let [a, b, c, d] = self.c0.finish().limbs();
            let [e, f, g, h] = self.c1.finish().limbs();
            E::from_limbs([a, b, c, d, e, f, g, h]).unwrap()
        }
    }
    /// Candidate exact accumulator for sums of `WideExact * WideExact`.
    /// Four canonical QM31 dot accumulators implement the outer quadratic tower.
    pub struct EbyEDot {
        ac: canonical::Dot,
        bd: canonical::Dot,
        ad: canonical::Dot,
        bc: canonical::Dot,
        count: usize,
    }
    impl EbyEDot {
        pub fn new() -> Self {
            Self {
                ac: canonical::Dot::new(),
                bd: canonical::Dot::new(),
                ad: canonical::Dot::new(),
                bc: canonical::Dot::new(),
                count: 0,
            }
        }
        #[inline(always)]
        pub fn push(&mut self, left: E, right: E) -> Result<(), ()> {
            if self.count >= MAX_TERMS { return Err(()); }
            let [a, b] = canonical::Q::from_wide(left);
            let [c, d] = canonical::Q::from_wide(right);
            self.ac.push(a, c);
            self.bd.push(b, d);
            self.ad.push(a, d);
            self.bc.push(b, c);
            self.count += 1;
            Ok(())
        }
        #[inline(always)]
        pub fn finish(self) -> E {
            let ac = qm31_of(self.ac.finish());
            let bd = qm31_of(self.bd.finish());
            let ad = qm31_of(self.ad.finish());
            let bc = qm31_of(self.bc.finish());
            E::new(ac.add(bd.mul(E::U)), ad.add(bc))
        }
    }
}
extern crate std;
pub mod r1_wire {
    //! UNPROVED COST PROBE. P2 D14-content wire; expanded row 25, isolated from the S4 gate.
    use crate::sampler::{circle_sample, qm31_sample, CircleRow};
    use alloc::vec::Vec;
    use aspis_core::circle::SecureCirclePoint;
    use aspis_core::field::{WideExact, QM31};
    use aspis_core::Digest32;
    pub const DOMAIN: &[u8] = b"UNPROVED:R1:PRIVATE-SALTED:SEMANTIC:P3";
    pub const LANES: usize = 29;
    pub const POINTS: usize = 3;
    pub const CLAIMS: usize = POINTS * LANES;
    pub const C1_LANES: [usize; 27] =
        [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
                20, 21, 22, 23, 24, 25, 28];
    pub const C2_LANES: [usize; 2] = [26, 27];
    pub type PointClaims = [[WideExact; LANES]; POINTS];
    pub enum Error {
        Allocation,
        RowOrder {
            expected: u8,
            actual: u8,
        },
        InvalidRow,
        Tag {
            row: u8,
        },
        Length {
            row: u8,
        },
        NonCanonical {
            row: u8,
            value: usize,
        },
        Boundary {
            round: usize,
        },
        Terminal,
        EqualCirclePoints,
        TrailingBytes,
        Public,
        ActivePole,
    }
    #[automatically_derived]
    #[doc(hidden)]
    unsafe impl ::core::clone::TrivialClone for Error { }
    #[automatically_derived]
    impl ::core::clone::Clone for Error {
        #[inline]
        fn clone(&self) -> Error {
            let _: ::core::clone::AssertParamIsClone<u8>;
            let _: ::core::clone::AssertParamIsClone<usize>;
            *self
        }
    }
    #[automatically_derived]
    impl ::core::marker::Copy for Error { }
    #[automatically_derived]
    impl ::core::fmt::Debug for Error {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            match self {
                Error::Allocation =>
                    ::core::fmt::Formatter::write_str(f, "Allocation"),
                Error::RowOrder { expected: __self_0, actual: __self_1 } =>
                    ::core::fmt::Formatter::debug_struct_field2_finish(f,
                        "RowOrder", "expected", __self_0, "actual", &__self_1),
                Error::InvalidRow =>
                    ::core::fmt::Formatter::write_str(f, "InvalidRow"),
                Error::Tag { row: __self_0 } =>
                    ::core::fmt::Formatter::debug_struct_field1_finish(f, "Tag",
                        "row", &__self_0),
                Error::Length { row: __self_0 } =>
                    ::core::fmt::Formatter::debug_struct_field1_finish(f,
                        "Length", "row", &__self_0),
                Error::NonCanonical { row: __self_0, value: __self_1 } =>
                    ::core::fmt::Formatter::debug_struct_field2_finish(f,
                        "NonCanonical", "row", __self_0, "value", &__self_1),
                Error::Boundary { round: __self_0 } =>
                    ::core::fmt::Formatter::debug_struct_field1_finish(f,
                        "Boundary", "round", &__self_0),
                Error::Terminal =>
                    ::core::fmt::Formatter::write_str(f, "Terminal"),
                Error::EqualCirclePoints =>
                    ::core::fmt::Formatter::write_str(f, "EqualCirclePoints"),
                Error::TrailingBytes =>
                    ::core::fmt::Formatter::write_str(f, "TrailingBytes"),
                Error::Public =>
                    ::core::fmt::Formatter::write_str(f, "Public"),
                Error::ActivePole =>
                    ::core::fmt::Formatter::write_str(f, "ActivePole"),
            }
        }
    }
    #[automatically_derived]
    impl ::core::marker::StructuralPartialEq for Error { }
    #[automatically_derived]
    impl ::core::cmp::PartialEq for Error {
        #[inline]
        fn eq(&self, other: &Error) -> bool {
            let __self_discr = ::core::intrinsics::discriminant_value(self);
            let __arg1_discr = ::core::intrinsics::discriminant_value(other);
            __self_discr == __arg1_discr &&
                match (self, other) {
                    (Error::RowOrder { expected: __self_0, actual: __self_1 },
                        Error::RowOrder { expected: __arg1_0, actual: __arg1_1 }) =>
                        __self_0 == __arg1_0 && __self_1 == __arg1_1,
                    (Error::Tag { row: __self_0 }, Error::Tag { row: __arg1_0 })
                        => __self_0 == __arg1_0,
                    (Error::Length { row: __self_0 }, Error::Length {
                        row: __arg1_0 }) => __self_0 == __arg1_0,
                    (Error::NonCanonical { row: __self_0, value: __self_1 },
                        Error::NonCanonical { row: __arg1_0, value: __arg1_1 }) =>
                        __self_0 == __arg1_0 && __self_1 == __arg1_1,
                    (Error::Boundary { round: __self_0 }, Error::Boundary {
                        round: __arg1_0 }) => __self_0 == __arg1_0,
                    _ => true,
                }
        }
    }
    #[automatically_derived]
    impl ::core::cmp::Eq for Error {
        #[inline]
        #[doc(hidden)]
        #[coverage(off)]
        fn assert_fields_are_eq(&self) {
            let _: ::core::cmp::AssertParamIsEq<u8>;
            let _: ::core::cmp::AssertParamIsEq<usize>;
        }
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
            let x =
                WideExact::from_le_bytes(bytes).ok_or(Error::NonCanonical {
                            row,
                            value,
                        })?;
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
        if record.len() != 5 + size { return Err(Error::Length { row }); }
        if record[0] != tag { return Err(Error::Tag { row }); }
        if u32::from_le_bytes([record[1], record[2], record[3], record[4]]) as
                    usize != size {
            return Err(Error::Length { row });
        }
        let payload = &record[5..];
        if row >= 14 { validate_record_fields(row, payload)?; }
        Ok(payload)
    }
    pub fn record(row: u8, payload: &[u8]) -> Result<Vec<u8>, Error> {
        let (tag, size) = row_shape(row).ok_or(Error::InvalidRow)?;
        if payload.len() != size { return Err(Error::Length { row }); }
        let mut out = Vec::with_capacity(5 + size);
        out.push(tag);
        out.extend_from_slice(&(size as u32).to_le_bytes());
        out.extend_from_slice(payload);
        parse_record(row, &out)?;
        Ok(out)
    }
    pub fn encode_values(values: impl IntoIterator<Item = WideExact>)
        -> Vec<u8> {
        let mut out = Vec::new();
        for value in values { out.extend_from_slice(&value.to_le_bytes()); }
        out
    }
    pub fn decode_values<const N : usize>(row: u8, payload: &[u8])
        -> Result<[WideExact; N], Error> {
        if payload.len() != 32 * N { return Err(Error::Length { row }); }
        let mut out = [WideExact::ZERO; N];
        for (value, bytes) in payload.chunks_exact(32).enumerate() {
            out[value] =
                WideExact::from_le_bytes(bytes).ok_or(Error::NonCanonical {
                            row,
                            value,
                        })?;
        }
        Ok(out)
    }
    /// A record whose framing and every field limb were checked by
    /// `parse_record`. Tokens are issued only from a successfully parsed Prefix;
    /// callers cannot supply a row separately from its bytes.
    pub(crate) struct ValidatedRecord<'a> {
        row: u8,
        framed: &'a [u8],
    }
    #[automatically_derived]
    #[doc(hidden)]
    unsafe impl<'a> ::core::clone::TrivialClone for ValidatedRecord<'a> { }
    #[automatically_derived]
    impl<'a> ::core::clone::Clone for ValidatedRecord<'a> {
        #[inline]
        fn clone(&self) -> ValidatedRecord<'a> {
            let _: ::core::clone::AssertParamIsClone<u8>;
            let _: ::core::clone::AssertParamIsClone<&'a [u8]>;
            *self
        }
    }
    #[automatically_derived]
    impl<'a> ::core::marker::Copy for ValidatedRecord<'a> { }
    impl<'a> ValidatedRecord<'a> {
        pub(crate) fn row(&self) -> u8 { self.row }
        pub(crate) fn framed(&self) -> &'a [u8] { self.framed }
        pub(crate) fn payload(&self) -> &'a [u8] { &self.framed[5..] }
        /// Decode checked base-field limbs from a semantic record. The
        /// validation token proves the 16-byte high half is zero and the
        /// low QM31 encoding canonical, while this method still checks the
        /// requested range and record class.
        pub(crate) fn decode_k<const N : usize>(&self, offset_values: usize)
            -> Result<[QM31; N], Error> {
            if self.row < 14 { return Err(Error::InvalidRow); }
            let byte_offset =
                offset_values.checked_mul(32).ok_or(Error::Length {
                            row: self.row,
                        })?;
            let byte_len =
                N.checked_mul(32).ok_or(Error::Length { row: self.row })?;
            let end =
                byte_offset.checked_add(byte_len).ok_or(Error::Length {
                            row: self.row,
                        })?;
            let bytes =
                self.payload().get(byte_offset..end).ok_or(Error::Length {
                            row: self.row,
                        })?;
            let mut out = [QM31::ZERO; N];
            for (value, part) in bytes.chunks_exact(32).enumerate() {
                out[value] =
                    QM31::from_le_bytes(&part[..16]).ok_or(Error::NonCanonical {
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
    pub struct SemanticTranscript<H: Digest32> {
        state: [u8; 32],
        hash: H,
        next_row: u8,
    }
    #[automatically_derived]
    impl<H: ::core::clone::Clone + Digest32> ::core::clone::Clone for
        SemanticTranscript<H> {
        #[inline]
        fn clone(&self) -> SemanticTranscript<H> {
            SemanticTranscript {
                state: ::core::clone::Clone::clone(&self.state),
                hash: ::core::clone::Clone::clone(&self.hash),
                next_row: ::core::clone::Clone::clone(&self.next_row),
            }
        }
    }
    impl<H: Digest32> SemanticTranscript<H> {
        pub fn new(hash: H, public_bytes: &[u8], c1_root: &[u8; 32])
            -> Result<Self, Error> {
            let length =
                u32::try_from(public_bytes.len()).map_err(|_| Error::Public)?;
            Ok(Self {
                    state: hash.digest(&[DOMAIN, &[0], &length.to_le_bytes(),
                                    public_bytes, c1_root]),
                    hash,
                    next_row: 0,
                })
        }
        pub fn state(&self) -> [u8; 32] { self.state }
        pub fn next_row(&self) -> u8 { self.next_row }
        fn sample_block_validated(&mut self, row: u8, framed: &[u8])
            -> Result<[u8; 32], Error> {
            if row != self.next_row {
                return Err(Error::RowOrder {
                            expected: self.next_row,
                            actual: row,
                        });
            }
            let absorbed =
                self.hash.digest(&[&self.state, &[0, 0xa0 + row], framed]);
            let block = self.hash.digest(&[&absorbed, &[1]]);
            self.state = self.hash.digest(&[&absorbed, &[2]]);
            self.next_row += 1;
            Ok(block)
        }
        fn sample_block(&mut self, row: u8, framed: &[u8])
            -> Result<[u8; 32], Error> {
            if row != self.next_row {
                return Err(Error::RowOrder {
                            expected: self.next_row,
                            actual: row,
                        });
            }
            parse_record(row, framed)?;
            self.sample_block_validated(row, framed)
        }
        pub(crate) fn semantic_validated(&mut self,
            record: ValidatedRecord<'_>) -> Result<QM31, Error> {
            let row = record.row();
            if row > 24 { return Err(Error::InvalidRow); }
            Ok(qm31_sample(&self.sample_block_validated(row,
                                record.framed())?))
        }
        pub(crate) fn circle_validated(&mut self, record: ValidatedRecord<'_>)
            -> Result<SecureCirclePoint, Error> {
            let row = record.row();
            let circle_row =
                match row {
                    25 => CircleRow::First,
                    26 => CircleRow::Second,
                    _ => return Err(Error::InvalidRow),
                };
            Ok(circle_sample(&self.sample_block_validated(row,
                                record.framed())?, circle_row))
        }
        pub fn semantic(&mut self, row: u8, framed: &[u8])
            -> Result<QM31, Error> {
            if row > 24 { return Err(Error::InvalidRow); }
            Ok(qm31_sample(&self.sample_block(row, framed)?))
        }
        /// R-B's one-block reference-circle map, including fixed fallback.
        /// The legacy Transcript method has a different parameter sampler.
        pub fn challenge_reference_circle_point(&mut self, row: u8,
            framed: &[u8]) -> Result<SecureCirclePoint, Error> {
            let circle_row =
                match row {
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
    fn parse_record_at<'a>(bytes: &'a [u8], row: u8, offset: usize)
        -> Result<(&'a [u8], usize), Error> {
        let length = 5 + row_shape(row).unwrap().1;
        let framed =
            bytes.get(offset..offset + length).ok_or(Error::Length { row })?;
        parse_record(row, framed)?;
        Ok((framed, offset + length))
    }
    impl<'a> Prefix<'a> {
        pub fn parse(bytes: &'a [u8]) -> Result<Self, Error> {
            if bytes.len() < 32 { return Err(Error::Length { row: 0 }); }
            let c1_root =
                match bytes[..32].try_into() {
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
            if offset != bytes.len() { return Err(Error::TrailingBytes); }
            Ok(Self {
                    c1_root,
                    records: [r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11,
                            r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23,
                            r24, r25, r26],
                })
        }
        pub fn record(&self, row: u8) -> Result<&'a [u8], Error> {
            if row >= 27 { return Err(Error::InvalidRow); }
            Ok(self.records[row as usize])
        }
        pub fn payload(&self, row: u8) -> Result<&'a [u8], Error> {
            let framed = self.record(row)?;
            Ok(&framed[5..])
        }
        pub(crate) fn validated_record(&self, row: u8)
            -> Result<ValidatedRecord<'a>, Error> {
            Ok(ValidatedRecord { row, framed: self.record(row)? })
        }
        /// Same row-25 decoder, with direct initialization of heap storage.
        pub fn point_claims_boxed(&self)
            -> Result<alloc::boxed::Box<PointClaims>, Error> {
            let payload = self.payload(25)?;
            if payload.len() != 32 * (CLAIMS + LANES) {
                return Err(Error::Length { row: 25 });
            }
            let mut out =
                aspis_core::r0::heap::uninit::<PointClaims>().map_err(|_|
                            Error::Allocation)?;
            unsafe {
                let p = out.as_mut_ptr().cast::<WideExact>();
                for j in 0..CLAIMS {
                    p.add(j).write(WideExact::from_le_bytes(&payload[j *
                                                    32..(j + 1) *
                                                    32]).ok_or(Error::NonCanonical { row: 25, value: j })?);
                }
                Ok(out.assume_init())
            }
        }
        pub fn point_claims(&self) -> Result<PointClaims, Error> {
            let flat =
                decode_values::<CLAIMS>(25,
                        &self.payload(25)?[..CLAIMS * 32])?;
            Ok(core::array::from_fn(|point|
                        {
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
    pub fn begin<H: Digest32>(prefix: &Prefix<'_>,
        transcript: &mut SemanticTranscript<H>) -> Result<Challenges, Error> {
        let lambda =
            transcript.semantic_validated(prefix.validated_record(0)?)?;
        let chi = transcript.semantic_validated(prefix.validated_record(1)?)?;
        let theta =
            transcript.semantic_validated(prefix.validated_record(2)?)?;
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
        let eta =
            transcript.semantic_validated(prefix.validated_record(14)?)?;
        Ok(Challenges { lambda, chi, theta, zc, mu, eta })
    }
}
pub mod r1_semantic {
    //! UNPROVED COST PROBE. P2 semantic layer in K plus the specified D14 tail.
    use crate::r1_wire::{
        self as wire, Challenges, Error, Prefix, SemanticTranscript,
    };
    use alloc::boxed::Box;
    use aspis_core::{Digest32, circle::SecureCirclePoint, field::QM31};
    use aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public;
    pub struct Verified<H: Digest32> {
        pub roots: [[u8; 32]; 2],
        pub challenges: Challenges,
        pub alpha: [QM31; 10],
        pub claims: Box<[[QM31; 29]; 3]>,
        pub extra: [QM31; 29],
        pub before_z1: [QM31; 29],
        pub state_before_z0: [u8; 32],
        pub z: [SecureCirclePoint; 2],
        pub transcript: SemanticTranscript<H>,
        pub round_checks: [[QM31; 3]; 10],
        pub terminal: QM31,
        pub masked_terminal: QM31,
    }
    pub fn decode<const N : usize>(row: u8, bytes: &[u8])
        -> Result<[QM31; N], Error> {
        if bytes.len() != N * 32 { return Err(Error::Length { row }); }
        let mut out = [QM31::ZERO; N];
        for (value, part) in bytes.chunks_exact(32).enumerate() {
            if part[16..].iter().any(|&b| b != 0) {
                return Err(Error::NonCanonical { row, value });
            }
            out[value] =
                QM31::from_le_bytes(&part[..16]).ok_or(Error::NonCanonical {
                            row,
                            value,
                        })?;
        }
        Ok(out)
    }
    #[inline(never)]
    fn claims(prefix: &Prefix<'_>) -> Result<Box<[[QM31; 29]; 3]>, Error> {
        let record = prefix.validated_record(25)?;
        let mut out =
            aspis_core::r0::heap::uninit::<[[QM31; 29]; 3]>().map_err(|_|
                        Error::Allocation)?;
        unsafe {
            for p in 0..3 {
                out.as_mut_ptr().cast::<[QM31; 29]>().add(p).write(record.decode_k::<29>(p
                                * 29)?);
            }
            Ok(out.assume_init())
        }
    }
    #[inline(never)]
    pub fn verify<H: Digest32>(public: Public<'_>, bytes: &[u8], hash: H)
        -> Result<Verified<H>, Error> {
        verify_observed(public, bytes, hash, None)
    }
    #[inline(always)]
    pub fn public_transcript<H: Digest32>(public: Public<'_>, hash: H,
        c1_root: &[u8; 32]) -> Result<SemanticTranscript<H>, Error> {
        SemanticTranscript::new(hash,
            &public.public_bytes().map_err(|_| Error::Public)?, c1_root)
    }
    fn mark(obs: crate::verifier::Observer, i: u8) { let _ = (obs, i); }
    fn semantic_boundary(polynomial: &[QM31; 28]) -> QM31 {
        let boundary =
            polynomial.iter().copied().fold(polynomial[0], QM31::add);
        boundary
    }
    fn semantic_value(polynomial: &[QM31; 28], alpha: &[QM31; 10],
        round: usize) -> QM31 {
        let value =
            polynomial.iter().rev().fold(QM31::ZERO,
                |a, &c| a.mul(alpha[round]).add(c));
        value
    }
    fn semantic_round<H: Digest32>(prefix: &Prefix<'_>,
        mut transcript: SemanticTranscript<H>, mut alpha: [QM31; 10],
        mut running: QM31, round: usize, mut round_checks: [[QM31; 3]; 10])
        ->
            Result<(QM31, [QM31; 10], SemanticTranscript<H>, [[QM31; 3]; 10]),
            Error> {
        let row = 15 + round as u8;
        let polynomial = prefix.validated_record(row)?.decode_k::<28>(0)?;
        let boundary = semantic_boundary(&polynomial);
        if boundary != running { return Err(Error::Boundary { round }); }
        alpha[round] =
            transcript.semantic_validated(prefix.validated_record(row)?)?;
        let value = semantic_value(&polynomial, &alpha, round);
        { round_checks[round] = [running, boundary, value]; }
        running = value;
        Ok((running, alpha, transcript, round_checks))
    }
    #[inline(never)]
    fn semantic_rounds<H: Digest32>(prefix: &Prefix<'_>,
        mut transcript: SemanticTranscript<H>)
        ->
            Result<(QM31, [QM31; 10], SemanticTranscript<H>, [[QM31; 3]; 10]),
            Error> {
        let mut running = prefix.validated_record(14)?.decode_k::<1>(0)?[0];
        let mut alpha = [QM31::ZERO; 10];
        let mut round_checks = [[QM31::ZERO; 3]; 10];
        {
            let round = 0usize;
            (running, alpha, transcript, round_checks) =
                semantic_round(prefix, transcript, alpha, running, round,
                        round_checks)?;
        }
        {
            let round = 1usize;
            (running, alpha, transcript, round_checks) =
                semantic_round(prefix, transcript, alpha, running, round,
                        round_checks)?;
        }
        {
            let round = 2usize;
            (running, alpha, transcript, round_checks) =
                semantic_round(prefix, transcript, alpha, running, round,
                        round_checks)?;
        }
        {
            let round = 3usize;
            (running, alpha, transcript, round_checks) =
                semantic_round(prefix, transcript, alpha, running, round,
                        round_checks)?;
        }
        {
            let round = 4usize;
            (running, alpha, transcript, round_checks) =
                semantic_round(prefix, transcript, alpha, running, round,
                        round_checks)?;
        }
        {
            let round = 5usize;
            (running, alpha, transcript, round_checks) =
                semantic_round(prefix, transcript, alpha, running, round,
                        round_checks)?;
        }
        {
            let round = 6usize;
            (running, alpha, transcript, round_checks) =
                semantic_round(prefix, transcript, alpha, running, round,
                        round_checks)?;
        }
        {
            let round = 7usize;
            (running, alpha, transcript, round_checks) =
                semantic_round(prefix, transcript, alpha, running, round,
                        round_checks)?;
        }
        {
            let round = 8usize;
            (running, alpha, transcript, round_checks) =
                semantic_round(prefix, transcript, alpha, running, round,
                        round_checks)?;
        }
        {
            let round = 9usize;
            (running, alpha, transcript, round_checks) =
                semantic_round(prefix, transcript, alpha, running, round,
                        round_checks)?;
        }
        Ok((running, alpha, transcript, round_checks))
    }
    #[inline(never)]
    fn verify_finish<H: Digest32>(public: Public<'_>, prefix: Prefix<'_>,
        mut transcript: SemanticTranscript<H>, challenges: Challenges,
        obs: crate::verifier::Observer) -> Result<Verified<H>, Error> {
        let (running, alpha, mut transcript, round_checks) =
            semantic_rounds(&prefix, transcript)?;
        mark(obs, 2);
        let claims = claims(&prefix)?;
        let original_challenges =
            aspis_core::state_only_prefix::r0::Challenges {
                lambda: challenges.lambda,
                chi: challenges.chi,
                theta: challenges.theta,
                zc: challenges.zc,
                mu: challenges.mu,
                eta: challenges.eta,
            };
        let terminal =
            public.terminal_qm31(&claims, &alpha,
                        &original_challenges).map_err(|_| Error::Public)?;
        mark(obs, 3);
        let mask =
            aspis_core::state_only_hiding::state_only_selected_mask_value(&core::array::from_fn(|i|
                            claims[0][i]), &core::array::from_fn(|i| claims[0][16 + i]),
                claims[0][27], &alpha);
        let extra = prefix.validated_record(25)?.decode_k::<29>(87)?;
        let masked_terminal =
            mask.add(challenges.eta.mul(terminal)).add(extra[28]);
        if running != masked_terminal { return Err(Error::Terminal); }
        mark(obs, 4);
        let state_before_z0 = transcript.state();
        let z0 = transcript.circle_validated(prefix.validated_record(25)?)?;
        let before_z1 = prefix.validated_record(26)?.decode_k::<29>(0)?;
        let z1 = transcript.circle_validated(prefix.validated_record(26)?)?;
        mark(obs, 5);
        {
            for (i, x) in [z0.x, z0.y, z1.x, z1.y].into_iter().enumerate() {
                crate::trace::value(3, i,
                    aspis_core::field::WideExact::from_qm31(x));
            }
            for (i, x) in
                challenges.with_alphas(&alpha).into_iter().enumerate() {
                crate::trace::value(0, i, x);
            }
            for (i, row) in round_checks.iter().enumerate() {
                for (j, x) in row.iter().enumerate() {
                    crate::trace::value(1, 3 * i + j,
                        aspis_core::field::WideExact::from_qm31(*x));
                }
            }
            crate::trace::value(2, 0,
                aspis_core::field::WideExact::from_qm31(terminal));
            crate::trace::value(2, 1,
                aspis_core::field::WideExact::from_qm31(masked_terminal));
        }
        if z0 == z1 { return Err(Error::EqualCirclePoints); }
        Ok(Verified {
                roots: [*prefix.c1_root,
                        prefix.payload(2)?.try_into().unwrap()],
                challenges,
                alpha,
                claims,
                extra,
                before_z1,
                state_before_z0,
                z: [z0, z1],
                transcript,
                round_checks,
                terminal,
                masked_terminal,
            })
    }
    #[inline(never)]
    pub fn verify_observed<H: Digest32>(public: Public<'_>, bytes: &[u8],
        hash: H, obs: crate::verifier::Observer)
        -> Result<Verified<H>, Error> {
        let prefix = Prefix::parse(bytes)?;
        mark(obs, 0);
        let mut transcript = public_transcript(public, hash, prefix.c1_root)?;
        let challenges = wire::begin(&prefix, &mut transcript)?;
        mark(obs, 1);
        verify_finish(public, prefix, transcript, challenges, obs)
    }
}
pub mod trace {
    //! UNPROVED COST PROBE. Native byte traces; compiled out of SBF.
    use aspis_core::field::WideExact as E;
    #[inline(always)]
    pub fn value(tag: u16, index: usize, x: E) { let _ = (tag, index, x); }
    pub fn take() -> alloc::vec::Vec<(u16, usize, [u8; 32])> {
        alloc::vec::Vec::new()
    }
}
pub mod transport {
    //! UNPROVED COST PROBE. S uses the D18 digit permutation; D uses retained D13.
    pub enum Variant { S1, S2, D, }
    #[automatically_derived]
    #[doc(hidden)]
    unsafe impl ::core::clone::TrivialClone for Variant { }
    #[automatically_derived]
    impl ::core::clone::Clone for Variant {
        #[inline]
        fn clone(&self) -> Variant { *self }
    }
    #[automatically_derived]
    impl ::core::marker::Copy for Variant { }
    #[automatically_derived]
    impl ::core::fmt::Debug for Variant {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            ::core::fmt::Formatter::write_str(f,
                match self {
                    Variant::S1 => "S1",
                    Variant::S2 => "S2",
                    Variant::D => "D",
                })
        }
    }
    #[automatically_derived]
    impl ::core::marker::StructuralPartialEq for Variant { }
    #[automatically_derived]
    impl ::core::cmp::PartialEq for Variant {
        #[inline]
        fn eq(&self, other: &Variant) -> bool {
            let __self_discr = ::core::intrinsics::discriminant_value(self);
            let __arg1_discr = ::core::intrinsics::discriminant_value(other);
            __self_discr == __arg1_discr
        }
    }
    #[automatically_derived]
    impl ::core::cmp::Eq for Variant {
        #[inline]
        #[doc(hidden)]
        #[coverage(off)]
        fn assert_fields_are_eq(&self) {}
    }
    pub const TAU: [usize; 5] = [3, 4, 2, 0, 1];
    impl Variant {
        pub fn tag(self) -> u8 {
            match self { Self::S1 => 1, Self::S2 => 2, Self::D => 3, }
        }
        pub fn from_tag(tag: u8) -> Option<Self> {
            match tag {
                1 => Some(Self::S1),
                2 => Some(Self::S2),
                3 => Some(Self::D),
                _ => None,
            }
        }
        pub fn folds(self) -> usize { if self == Self::S1 { 1 } else { 2 } }
        pub fn final_len(self) -> usize { 1024 >> (2 * self.folds()) }
        pub fn row(self, j: usize) -> usize {
            if self == Self::D {
                return aspis_core::r0::transport::COEFFICIENT_TO_ROW[j] as
                        usize;
            }
            let mut out = 0;
            for d in 0..5 { out |= ((j >> (2 * d)) & 3) << (2 * TAU[d]); }
            out
        }
        pub fn coefficients<T: Copy>(self, rows: &[T; 1024]) -> [T; 1024] {
            core::array::from_fn(|j| rows[self.row(j)])
        }
        pub fn rows<T: Copy>(self, coefficients: &[T; 1024]) -> [T; 1024] {
            let mut out = *coefficients;
            for j in 0..1024 { out[self.row(j)] = coefficients[j]; }
            out
        }
    }
}
pub mod weights {
    //! UNPROVED COST PROBE. Seven coefficient functionals and their dual folds.
    use alloc::{boxed::Box, vec::Vec};
    use aspis_core::{
        field::{QM31 as K, WideExact as E, M31},
        circle::SecureCirclePoint,
    };
    use crate::{
        transport::{Variant, TAU},
        verifier::Error,
    };
    pub const QUARTER: M31 = M31(536870912);
    pub const PERM: [usize; 4] = [0, 3, 2, 1];
    pub fn powers<const N : usize>(x: E) -> [E; N] {
        let mut out = [E::ZERO; N];
        let mut p = E::ONE;
        let mut i = 0usize;
        while i < N {
            out[i] = p;
            i += 1;
            if i == N { return out; }
            p = p.mul(x);
        }
        out
    }
    pub fn kpowers<const N : usize>(x: K) -> [K; N] {
        let mut out = [K::ZERO; N];
        let mut p = K::ONE;
        for i in 0..N { out[i] = p; p = p.mul(x); }
        out
    }
    pub fn double(x: K) -> K { x.mul(x).add(x.mul(x)).sub(K::ONE) }
    pub fn field(bytes: &[u8], i: usize) -> E {
        E::from_le_bytes(&bytes[i * 32..(i + 1) * 32]).unwrap()
    }
    const S2_INACTIVE_GROUPS: [u8; 64] =
        [0, 1, 2, 3, 4, 5, 5, 6, 4, 5, 5, 5, 7, 7, 7, 7, 7, 7, 7, 4, 4, 5, 5,
                6, 4, 5, 5, 5, 7, 7, 7, 4, 7, 7, 7, 7, 4, 5, 5, 5, 4, 5, 5, 5,
                8, 9, 10, 8, 11, 2, 2, 10, 4, 5, 5, 6, 4, 5, 5, 6, 7, 7, 7,
                7];
    const S2_INACTIVE_MASKS: [u16; 12] =
        [32769, 49217, 49280, 16448, 32767, 16383, 49151, 65535, 49152, 57344,
                49216, 33024];
    #[inline(never)]
    fn s2_grouped_inactive_pair(f: &[u8], low: &[E; 16]) -> E {
        let mut coefficients = [E::ZERO; 12];
        for j in 0..64 {
            let group = S2_INACTIVE_GROUPS[j] as usize;
            coefficients[group] = coefficients[group].add(field(f, j));
        }
        let mut pair = E::ZERO;
        for group in 0..12 {
            let mut weight = E::ZERO;
            for bit in 0..16 {
                let challenge = low[bit];
                if S2_INACTIVE_MASKS[group] & (1 << bit) != 0 {
                    weight = weight.add(challenge);
                }
            }
            pair = pair.add(coefficients[group].mul(weight));
        }
        pair
    }
    /// Contract the inactive row after combining coefficients with the same
    /// sixteen-entry inactive mask. The zero mask is retained as a group; its
    /// subset weight is zero, matching the ungrouped sum.
    #[inline(never)]
    fn grouped_inactive_pair(weights: &Weights, f: &[u8], low: &[E; 16])
        -> E {
        if weights.variant == Variant::S2 && f.len() == 64 * 32 {
            return s2_grouped_inactive_pair(f, low);
        }
        let mut group_masks = [0u16; 64];
        let mut group_coefficients = [E::ZERO; 64];
        let mut groups = 0;
        for j in 0..f.len() / 32 {
            let mut mask = 0u16;
            for s in 0..16 {
                if weights.raw(0, 16 * j + s) == K::ONE { mask |= 1 << s; }
            }
            let coefficient = field(f, j);
            let mut group = 0;
            while group < groups && group_masks[group] != mask { group += 1; }
            if group == groups { group_masks[group] = mask; groups += 1; }
            group_coefficients[group] =
                group_coefficients[group].add(coefficient);
        }
        let mut pair = E::ZERO;
        for group in 0..groups {
            let mask = group_masks[group];
            let mut weight = E::ZERO;
            for s in 0..16 {
                let challenge = low[s];
                if mask & (1 << s) != 0 { weight = weight.add(challenge); }
            }
            pair = pair.add(group_coefficients[group].mul(weight));
        }
        pair
    }
    /// Build the four two-fold Libra dual weights without per-cell exponentiation.
    #[inline(never)]
    fn twofold_libra_weights(low: &[E; 16], extra: [K; 2]) -> [E; 4] {
        let mut powers = [[K::ZERO; 28]; 2];
        for side in 0..2 {
            let mut power = K::ONE;
            for index in 0..28 {
                powers[side][index] = power;
                power = power.mul(extra[side]);
            }
        }
        let mut out = [E::ZERO; 4];
        for j in 0..4 {
            let mut weight = E::ZERO;
            for s in 0..16 {
                let index = 16 * j + s;
                if index < 56 {
                    weight =
                        weight.add(low[s].mul_qm31(powers[index / 28][index % 28]));
                }
            }
            out[j] = weight;
        }
        out
    }
    /// Exact factorization of the existing 56-entry Libra row into two 28-entry
    /// geometric runs. The 16-entry low tensor is a product of two four-entry
    /// tensors; the only cut blocks have lengths 12 and 4 (28 = 16 + 12).
    #[inline(never)]
    fn factored_s2_libra_weights(ap0: &[E; 4], ap1: &[E; 4], extra: [K; 2])
        -> [E; 4] {
        let mut weights = [E::ZERO; 4];
        for side in 0..2 {
            let q0 = K::ONE;
            let q1 = q0.mul(extra[side]);
            let q2 = q1.mul(extra[side]);
            let q3 = q2.mul(extra[side]);
            let _q4 = q3.mul(extra[side]);
            let q = [q0, q1, q2, q3];
            let q4 = q[2].square();
            let q8 = q4.square();
            let q12 = q8.mul(q4);
            let q16 = q8.square();
            let low = Weights::scalar_factor(&q, ap0);
            let high_powers = [K::ONE, q4, q8, q12];
            let term0 =
                ap1[PERM[0]].mul_qm31(high_powers[0]).mul_m31(QUARTER);
            let term1 =
                ap1[PERM[1]].mul_qm31(high_powers[1]).mul_m31(QUARTER);
            let term2 =
                ap1[PERM[2]].mul_qm31(high_powers[2]).mul_m31(QUARTER);
            let term3 =
                ap1[PERM[3]].mul_qm31(high_powers[3]).mul_m31(QUARTER);
            let terms = [term0, term1, term2, term3];
            let first2 = terms[0].add(terms[1]);
            let first3 = first2.add(terms[2]);
            let all = first3.add(terms[3]);
            if side == 0 {
                weights[0] = low.mul(all);
                weights[1] = low.mul(first3).mul_qm31(q16);
            } else {
                weights[1] =
                    weights[1].add(low.mul(ap1[PERM[3]].mul_m31(QUARTER)));
                weights[2] = low.mul(all).mul_qm31(q4);
                weights[3] = low.mul(first2).mul_qm31(q16.mul(q4));
            }
        }
        weights
    }
    fn shared_two_point_guard(w: &Weights, folds: usize) -> bool {
        w.variant == Variant::S2 && folds == 2 &&
                w.factors[0][2] == w.factors[2][2] &&
            w.factors[0][3] == w.factors[2][3]
    }
    fn push_byte_products(pair: &mut crate::fast_pairing::EbyKDot, f: &[u8],
        scratch: &[K], n: usize) -> Result<(), Error> {
        for j in 0..n {
            match pair.push(field(f, j), scratch[j]) {
                Ok(()) => {}
                Err(_) => return Err(Error::Parse),
            }
        }
        Ok(())
    }
    fn partial_dot(f: &[u8], common: &[K; 16], s: usize) -> Result<E, Error> {
        let mut dot = crate::fast_pairing::EbyKDot::new();
        for j in 0..16 {
            match dot.push(field(f, 16 * s + j), common[j]) {
                Ok(()) => {}
                Err(_) => return Err(Error::Parse),
            }
        }
        Ok(dot.finish())
    }
    fn high_dot(partials: &[E; 4], coeffs: &[K; 4]) -> Result<E, Error> {
        let mut high = crate::fast_pairing::EbyKDot::new();
        for s in 0..4 {
            match high.push(partials[s], coeffs[s]) {
                Ok(()) => {}
                Err(_) => return Err(Error::Parse),
            }
        }
        Ok(high.finish())
    }
    fn process_regular_kinds(w: &Weights, shared_two_point: bool, alpha: &[E],
        f: &[u8], folds: usize, n: usize, ap0: &[E; 4], ap1: &[E; 4],
        scratch: &mut Vec<K>, parts: &mut [E; 7]) -> Result<(), Error> {
        if !shared_two_point {
            process_kind(w, 1, alpha, f, folds, n, ap0, ap1, scratch, parts)?;
        }
        process_kind(w, 2, alpha, f, folds, n, ap0, ap1, scratch, parts)?;
        if !shared_two_point {
            process_kind(w, 3, alpha, f, folds, n, ap0, ap1, scratch, parts)?;
        }
        process_kind(w, 5, alpha, f, folds, n, ap0, ap1, scratch, parts)?;
        process_kind(w, 6, alpha, f, folds, n, ap0, ap1, scratch, parts)?;
        Ok(())
    }
    fn shared_partials(f: &[u8], common: &[K; 16]) -> Result<[E; 4], Error> {
        let mut partials = [E::ZERO; 4];
        for s in 0..4 { partials[s] = partial_dot(f, common, s)?; }
        Ok(partials)
    }
    fn shared_high(partials: &[E; 4], w: &Weights, ap0: &[E; 4], ap1: &[E; 4],
        parts: &mut [E; 7]) -> Result<(), Error> {
        let high0 = high_dot(partials, &w.factors[0][4])?;
        let scale0 =
            Weights::scalar_factor(&w.factors[0][0],
                    ap0).mul(Weights::scalar_factor(&w.factors[0][1], ap1));
        parts[1] = scale0.mul(high0);
        let high2 = high_dot(partials, &w.factors[2][4])?;
        let scale2 =
            Weights::scalar_factor(&w.factors[2][0],
                    ap0).mul(Weights::scalar_factor(&w.factors[2][1], ap1));
        parts[3] = scale2.mul(high2);
        Ok(())
    }
    fn process_kind(w: &Weights, kind: usize, alpha: &[E], f: &[u8],
        folds: usize, n: usize, ap0: &[E; 4], ap1: &[E; 4],
        scratch: &mut Vec<K>, parts: &mut [E; 7]) -> Result<(), Error> {
        if w.variant == Variant::D && kind < 4 {
            parts[kind] = w.dense_point_pair(kind, alpha, f)?;
        } else {
            let k = if kind < 4 { kind - 1 } else { kind - 2 };
            w.tensor(k, folds, scratch);
            let mut scale = Weights::scalar_factor(&w.factors[k][0], ap0);
            if folds == 2 {
                scale =
                    scale.mul(Weights::scalar_factor(&w.factors[k][1], ap1));
            }
            let mut pair = crate::fast_pairing::EbyKDot::new();
            push_byte_products(&mut pair, f, scratch, n)?;
            parts[kind] = scale.mul(pair.finish());
        }
        Ok(())
    }
    pub struct Weights {
        pub variant: Variant,
        pub factors: [[[K; 4]; 5]; 5],
        pub points: [[K; 10]; 3],
        pub extra: [K; 2],
    }
    impl Weights {
        #[inline(never)]
        fn box_from_parts(variant: Variant, factors: [[[K; 4]; 5]; 5],
            points: [[K; 10]; 3], extra: [K; 2]) -> Box<Self> {
            Box::new(Self { variant, factors, points, extra })
        }
        #[inline(never)]
        pub fn new(variant: Variant, alpha: &[K; 10],
            z: &[SecureCirclePoint; 2]) -> Result<Box<Self>, Error> {
            let points =
                aspis_core::state_only_prefix::r0::statement_points(alpha);
            let extra = [alpha[8], alpha[9]];
            let mut factors = [[[K::ZERO; 4]; 5]; 5];
            for k in 0..3 {
                for d in 0..5 {
                    let a = points[k][9 - 2 * TAU[d]];
                    let b = points[k][8 - 2 * TAU[d]];
                    factors[k][d] =
                        [K::ONE.sub(a).mul(K::ONE.sub(b)), a.mul(K::ONE.sub(b)),
                                K::ONE.sub(a).mul(b), a.mul(b)];
                }
            }
            for k in 0..2 {
                factors[3 + k][0] =
                    [K::ONE, z[k].y, z[k].x, z[k].x.mul(z[k].y)];
                let mut x = double(z[k].x);
                for d in 1..5 {
                    let y = double(x);
                    factors[3 + k][d] = [K::ONE, x, y, x.mul(y)];
                    x = double(y);
                }
            }
            Ok(Self::box_from_parts(variant, factors, points, extra))
        }
        pub fn raw(&self, kind: usize, j: usize) -> K {
            match kind {
                0 =>
                    if aspis_core::r0::opening::inactive(self.variant.row(j)).unwrap()
                        {
                        K::ONE
                    } else { K::ZERO },
                4 =>
                    if j < 56 {
                        self.extra[j / 28].pow((j % 28) as u64)
                    } else { K::ZERO },
                1..=3 if self.variant == Variant::D => {
                    let r = self.variant.row(j);
                    (0..10).fold(K::ONE,
                        |v, b|
                            v.mul(if r & (1 << b) == 0 {
                                    K::ONE.sub(self.points[kind - 1][9 - b])
                                } else { self.points[kind - 1][9 - b] }))
                }
                _ => {
                    let k = if kind < 4 { kind - 1 } else { kind - 2 };
                    (0..5).fold(K::ONE,
                        |v, d| v.mul(self.factors[k][d][(j >> (2 * d)) & 3]))
                }
            }
        }
        fn scalar_factor(f: &[K; 4], p: &[E; 4]) -> E {
            (0..4).fold(E::ZERO,
                    |v, s| v.add(p[PERM[s]].mul_qm31(f[s]))).mul_m31(QUARTER)
        }
        fn tensor(&self, k: usize, folds: usize, output: &mut [K]) {
            output[0] = K::ONE;
            let mut n = 1;
            for d in folds..5 {
                for j in (0..n).rev() {
                    let x = output[j];
                    output[j + 0 * n] = x.mul(self.factors[k][d][0]);
                    output[j + 1 * n] = x.mul(self.factors[k][d][1]);
                    output[j + 2 * n] = x.mul(self.factors[k][d][2]);
                    output[j + 3 * n] = x.mul(self.factors[k][d][3]);
                }
                n *= 4;
            }
        }
        pub fn dual_raw(&self, kind: usize, j: usize, alpha: &[E]) -> E {
            let p0 = powers::<4>(alpha[0]);
            let p1 =
                if alpha.len() == 2 {
                    powers::<4>(alpha[1])
                } else { [E::ONE; 4] };
            let width = 1 << (2 * alpha.len());
            let mut sum = E::ZERO;
            for s in 0..width {
                let p = p0[PERM[s % 4]].mul(p1[PERM[s / 4]]);
                sum = sum.add(p.mul_qm31(self.raw(kind, width * j + s)));
            }
            for _ in alpha { sum = sum.mul_m31(QUARTER); }
            sum
        }
        /// Product rows keep a K tensor after their low digits have been folded.
        /// Only the contracted scalar is in E. Sparse rows are handled separately.
        #[inline(never)]
        pub fn pair(&self, alpha: &[E], f: &[u8], kappa: E)
            -> Result<E, Error> {
            let n = f.len() / 32;
            let folds = alpha.len();
            let mut expected_n = 1024usize;
            for _ in 0..folds { expected_n = expected_n >> 2u32; }
            if n != expected_n { return Err(Error::Parse); }
            let ap0 = powers::<4>(alpha[0]);
            let ap1 =
                if folds == 2 { powers::<4>(alpha[1]) } else { [E::ONE; 4] };
            let mut scratch =
                match aspis_core::r0::heap::filled(n, K::ZERO) {
                    Ok(v) => v,
                    Err(_) => return Err(Error::Allocation),
                };
            let mut parts = [E::ZERO; 7];
            let shared_two_point = shared_two_point_guard(self, folds);
            process_regular_kinds(self, shared_two_point, alpha, f, folds, n,
                    &ap0, &ap1, &mut scratch, &mut parts)?;
            if shared_two_point {
                let mut common = [K::ZERO; 16];
                for j in 0..16 {
                    common[j] =
                        self.factors[0][2][j &
                                    3].mul(self.factors[0][3][j >> 2u32]);
                }
                let partials = shared_partials(f, &common)?;
                shared_high(&partials, self, &ap0, &ap1, &mut parts)?;
            }
            if folds == 1 {
                let mut dual = [E::ZERO; 16];
                for mask in 0..16 {
                    let mut weight = E::ZERO;
                    for s in 0..4 {
                        if mask & (1usize << (s as u32)) != 0 {
                            weight = weight.add(ap0[PERM[s]]);
                        }
                    }
                    dual[mask] = weight.mul_m31(QUARTER);
                }
                let mut groups = [E::ZERO; 16];
                for j in 0..n {
                    let mut mask = 0;
                    for s in 0..4 {
                        if self.raw(0, 4 * j + s) == K::ONE {
                            mask |= 1usize << (s as u32);
                        }
                    }
                    groups[mask] = groups[mask].add(field(f, j));
                }
                for m in 1..16 {
                    parts[0] = parts[0].add(groups[m].mul(dual[m]));
                }
                for side in 0..2 {
                    let p = kpowers::<5>(self.extra[side]);
                    let scale =
                        Self::scalar_factor(&[p[0], p[1], p[2], p[3]], &ap0);
                    let mut power = K::ONE;
                    let mut pair = E::ZERO;
                    for j in 0..7 {
                        pair = pair.add(field(f, j + 7 * side).mul_qm31(power));
                        power = power.mul(p[4]);
                    }
                    parts[4] = parts[4].add(pair.mul(scale));
                }
            } else {
                let mut low = [E::ZERO; 16];
                for s in 0..16 {
                    low[s] =
                        ap0[PERM[s %
                                            4]].mul(ap1[PERM[s / 4]]).mul_m31(QUARTER.mul(QUARTER));
                }
                parts[0] = grouped_inactive_pair(self, f, &low);
                let libra =
                    if self.variant == Variant::S2 {
                        factored_s2_libra_weights(&ap0, &ap1, self.extra)
                    } else { twofold_libra_weights(&low, self.extra) };
                for j in 0..4 {
                    parts[4] = parts[4].add(field(f, j).mul(libra[j]));
                }
            }
            for kind in 0..7 {
                for j in 0..1024 {
                    crate::trace::value(6, kind * 1024 + j,
                        E::from_qm31(self.raw(kind, j)));
                }
                for j in 0..n {
                    crate::trace::value(7, kind * n + j,
                        self.dual_raw(kind, j, alpha));
                }
            }
            let k = powers::<7>(kappa);
            let mut sum = E::ZERO;
            for kind in 0..7 {
                crate::trace::value(8, kind, parts[kind]);
                sum = sum.add(k[kind].mul(parts[kind]));
            }
            Ok(sum)
        }
        #[inline(never)]
        fn dense_point_pair(&self, kind: usize, alpha: &[E], f: &[u8])
            -> Result<E, Error> {
            let mut rows =
                match aspis_core::r0::heap::filled(1024, K::ZERO) {
                    Ok(v) => v,
                    Err(_) => return Err(Error::Allocation),
                };
            rows[0] = K::ONE;
            let mut width = 1;
            for b in 0..10 {
                let p = self.points[kind - 1][9 - b];
                for j in (0..width).rev() {
                    let x = rows[j];
                    rows[j + width] = x.mul(p);
                    rows[j] = x.mul(K::ONE.sub(p));
                }
                width *= 2;
            }
            let a = powers::<4>(alpha[0]);
            let b = powers::<4>(alpha[1]);
            let mut low = [E::ZERO; 16];
            for s in 0..16 {
                low[s] =
                    a[PERM[s %
                                        4]].mul(b[PERM[s / 4]]).mul_m31(QUARTER.mul(QUARTER));
            }
            let mut pair = E::ZERO;
            for j in 0..64 {
                let mut w = E::ZERO;
                for s in 0..16 {
                    w =
                        w.add(low[s].mul_qm31(rows[self.variant.row(16 * j + s)]));
                }
                pair = pair.add(field(f, j).mul(w));
            }
            Ok(pair)
        }
        pub fn materialize(&self, kappa: E) -> Result<Vec<E>, Error> {
            let kp = powers::<7>(kappa);
            let mut w =
                match aspis_core::r0::heap::filled(1024, E::ZERO) {
                    Ok(v) => v,
                    Err(_) => return Err(Error::Allocation),
                };
            for (j, v) in w.iter_mut().enumerate() {
                for kind in 0..7 {
                    *v = v.add(kp[kind].mul_qm31(self.raw(kind, j)));
                }
            }
            Ok(w)
        }
    }
}
pub mod transcript {
    //! UNPROVED COST PROBE. Explicit opening schedule, including rho after queries.
    use aspis_core::r0::CodeField;
    use aspis_core::{Digest32, field::WideExact as E};
    use crate::transport::Variant;
    pub struct Transcript<H: Digest32> {
        pub state: [u8; 32],
        hash: H,
    }
    impl<H: Digest32> Transcript<H> {
        pub fn new(hash: H, semantic_state: [u8; 32], variant: Variant)
            -> Self {
            let domain: &[u8] = b"UNPROVED:R1:PRIVATE-SALTED:P3";
            Self {
                state: hash.digest(&[domain, &[variant.tag()],
                                &semantic_state]),
                hash,
            }
        }
        pub fn absorb(&mut self, row: u8, payload: &[u8]) {
            self.state =
                self.hash.digest(&[&self.state, &[0, 0xa0 + row],
                                &(payload.len() as u32).to_le_bytes(), payload]);
        }
        pub fn block(&mut self, row: u8, payload: &[u8]) -> [u8; 32] {
            self.absorb(row, payload);
            let block = self.hash.digest(&[&self.state, &[1]]);
            self.state = self.hash.digest(&[&self.state, &[2]]);
            block
        }
        pub fn scalar(&mut self, row: u8, payload: &[u8], nonzero: bool)
            -> E {
            let block = self.block(row, payload);
            let out =
                if nonzero {
                    crate::sampler::gamma_sample(&block)
                } else { crate::sampler::ordinary_sample(&block) };
            crate::trace::value(4, row as usize, out);
            out
        }
        /// Final query-residual batching: at most 22 coefficients, so a nonzero
        /// residual has at most 21 roots even when sampled from the K subfield.
        /// Gamma and both folding challenges continue to use E.
        pub fn scalar_k(&mut self, row: u8, payload: &[u8])
            -> aspis_core::field::QM31 {
            let out = crate::sampler::qm31_sample(&self.block(row, payload));
            crate::trace::value(4, row as usize, E::from_qm31(out));
            out
        }
        pub fn queries(&mut self, row: u8, payload: &[u8])
            -> Result<[u32; 22], crate::verifier::Error> {
            self.absorb(row, payload);
            let mut blocks = [[0; 32]; 8];
            let mut advances = blocks;
            let mut state = self.state;
            blocks[0] = self.hash.digest(&[&state, &[1]]);
            advances[0] = self.hash.digest(&[&state, &[2]]);
            state = advances[0];
            blocks[1] = self.hash.digest(&[&state, &[1]]);
            advances[1] = self.hash.digest(&[&state, &[2]]);
            state = advances[1];
            blocks[2] = self.hash.digest(&[&state, &[1]]);
            advances[2] = self.hash.digest(&[&state, &[2]]);
            state = advances[2];
            blocks[3] = self.hash.digest(&[&state, &[1]]);
            advances[3] = self.hash.digest(&[&state, &[2]]);
            state = advances[3];
            blocks[4] = self.hash.digest(&[&state, &[1]]);
            advances[4] = self.hash.digest(&[&state, &[2]]);
            state = advances[4];
            blocks[5] = self.hash.digest(&[&state, &[1]]);
            advances[5] = self.hash.digest(&[&state, &[2]]);
            state = advances[5];
            blocks[6] = self.hash.digest(&[&state, &[1]]);
            advances[6] = self.hash.digest(&[&state, &[2]]);
            state = advances[6];
            blocks[7] = self.hash.digest(&[&state, &[1]]);
            advances[7] = self.hash.digest(&[&state, &[2]]);
            state = advances[7];
            let (q, state) =
                aspis_core::r0_transcript::queries_from_pairs(&blocks,
                            &advances).map_err(|_| crate::verifier::Error::Transcript)?;
            self.state = state;
            {
                let u = q[0];
                crate::trace::value(5, 0,
                    E::from_m31(aspis_core::field::M31(u)));
            }
            {
                let u = q[1];
                crate::trace::value(5, 1,
                    E::from_m31(aspis_core::field::M31(u)));
            }
            {
                let u = q[2];
                crate::trace::value(5, 2,
                    E::from_m31(aspis_core::field::M31(u)));
            }
            {
                let u = q[3];
                crate::trace::value(5, 3,
                    E::from_m31(aspis_core::field::M31(u)));
            }
            {
                let u = q[4];
                crate::trace::value(5, 4,
                    E::from_m31(aspis_core::field::M31(u)));
            }
            {
                let u = q[5];
                crate::trace::value(5, 5,
                    E::from_m31(aspis_core::field::M31(u)));
            }
            {
                let u = q[6];
                crate::trace::value(5, 6,
                    E::from_m31(aspis_core::field::M31(u)));
            }
            {
                let u = q[7];
                crate::trace::value(5, 7,
                    E::from_m31(aspis_core::field::M31(u)));
            }
            {
                let u = q[8];
                crate::trace::value(5, 8,
                    E::from_m31(aspis_core::field::M31(u)));
            }
            {
                let u = q[9];
                crate::trace::value(5, 9,
                    E::from_m31(aspis_core::field::M31(u)));
            }
            {
                let u = q[10];
                crate::trace::value(5, 10,
                    E::from_m31(aspis_core::field::M31(u)));
            }
            {
                let u = q[11];
                crate::trace::value(5, 11,
                    E::from_m31(aspis_core::field::M31(u)));
            }
            {
                let u = q[12];
                crate::trace::value(5, 12,
                    E::from_m31(aspis_core::field::M31(u)));
            }
            {
                let u = q[13];
                crate::trace::value(5, 13,
                    E::from_m31(aspis_core::field::M31(u)));
            }
            {
                let u = q[14];
                crate::trace::value(5, 14,
                    E::from_m31(aspis_core::field::M31(u)));
            }
            {
                let u = q[15];
                crate::trace::value(5, 15,
                    E::from_m31(aspis_core::field::M31(u)));
            }
            {
                let u = q[16];
                crate::trace::value(5, 16,
                    E::from_m31(aspis_core::field::M31(u)));
            }
            {
                let u = q[17];
                crate::trace::value(5, 17,
                    E::from_m31(aspis_core::field::M31(u)));
            }
            {
                let u = q[18];
                crate::trace::value(5, 18,
                    E::from_m31(aspis_core::field::M31(u)));
            }
            {
                let u = q[19];
                crate::trace::value(5, 19,
                    E::from_m31(aspis_core::field::M31(u)));
            }
            {
                let u = q[20];
                crate::trace::value(5, 20,
                    E::from_m31(aspis_core::field::M31(u)));
            }
            {
                let u = q[21];
                crate::trace::value(5, 21,
                    E::from_m31(aspis_core::field::M31(u)));
            }
            Ok(q)
        }
    }
}
pub mod verifier {
    //! UNPROVED R1 COST PROBE. Two-transaction verifier shape; no production use.
    use aspis_core::r0::CodeField;
    use alloc::{boxed::Box, vec::Vec};
    use aspis_core::{
        Digest32, field::{WideExact as E, QM31 as K, M31},
        circle::SecureCirclePoint, r0::{domain, merkle},
    };
    use aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public;
    use crate::{
        transport::Variant, weights::{Weights, field, powers, QUARTER},
        transcript::Transcript,
    };
    pub const SEMANTIC_BYTES: usize = 12903 + 29 * 32;
    pub const HEADER: usize = 16;
    pub const INITIAL_QUERY_BYTES: usize = 480 + 128 + 64 + 2 * 6 * 7 * 32;
    pub const SECOND_QUERY_BYTES: usize = 4 * 32 + 32 + 6 * 7 * 32;
    pub const CHECKPOINT_FIXED: usize =
        16 + 32 * 3 + 64 + 32 * 4 + 16 + 88 + 160 + 64 + 32 * 2 + 16 + 32;
    pub enum Error {
        Parse,
        Semantic,
        Transcript,
        Relation,
        Merkle,
        Query,
        Checkpoint,
        Allocation,

        /// Host prover only (LOG D38.3): this attempt's challenges fail the public
        /// P_R1 check. Carries no challenge and no conjunct.
        Rejected,

        /// Host prover only (D38.3): all N = 8 attempts were rejected; nothing is published.
        AttemptsExhausted,

        /// Host prover only: the operating-system entropy source failed.
        Entropy,
    }
    #[automatically_derived]
    impl ::core::fmt::Debug for Error {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            ::core::fmt::Formatter::write_str(f,
                match self {
                    Error::Parse => "Parse",
                    Error::Semantic => "Semantic",
                    Error::Transcript => "Transcript",
                    Error::Relation => "Relation",
                    Error::Merkle => "Merkle",
                    Error::Query => "Query",
                    Error::Checkpoint => "Checkpoint",
                    Error::Allocation => "Allocation",
                    Error::Rejected => "Rejected",
                    Error::AttemptsExhausted => "AttemptsExhausted",
                    Error::Entropy => "Entropy",
                })
        }
    }
    #[automatically_derived]
    #[doc(hidden)]
    unsafe impl ::core::clone::TrivialClone for Error { }
    #[automatically_derived]
    impl ::core::clone::Clone for Error {
        #[inline]
        fn clone(&self) -> Error { *self }
    }
    #[automatically_derived]
    impl ::core::marker::Copy for Error { }
    #[automatically_derived]
    impl ::core::marker::StructuralPartialEq for Error { }
    #[automatically_derived]
    impl ::core::cmp::PartialEq for Error {
        #[inline]
        fn eq(&self, other: &Error) -> bool {
            let __self_discr = ::core::intrinsics::discriminant_value(self);
            let __arg1_discr = ::core::intrinsics::discriminant_value(other);
            __self_discr == __arg1_discr
        }
    }
    #[automatically_derived]
    impl ::core::cmp::Eq for Error {
        #[inline]
        #[doc(hidden)]
        #[coverage(off)]
        fn assert_fields_are_eq(&self) {}
    }
    pub enum Phase {
        Parsed,
        Semantic,
        SemanticPart(u8),
        Prepare,
        CheckpointRead,
        Merkle(usize),
        Query(usize),
        QueryPart(usize, u8),
        CheckpointWrite,
        Relation,
        Final,
    }
    #[automatically_derived]
    impl ::core::fmt::Debug for Phase {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            match self {
                Phase::Parsed =>
                    ::core::fmt::Formatter::write_str(f, "Parsed"),
                Phase::Semantic =>
                    ::core::fmt::Formatter::write_str(f, "Semantic"),
                Phase::SemanticPart(__self_0) =>
                    ::core::fmt::Formatter::debug_tuple_field1_finish(f,
                        "SemanticPart", &__self_0),
                Phase::Prepare =>
                    ::core::fmt::Formatter::write_str(f, "Prepare"),
                Phase::CheckpointRead =>
                    ::core::fmt::Formatter::write_str(f, "CheckpointRead"),
                Phase::Merkle(__self_0) =>
                    ::core::fmt::Formatter::debug_tuple_field1_finish(f,
                        "Merkle", &__self_0),
                Phase::Query(__self_0) =>
                    ::core::fmt::Formatter::debug_tuple_field1_finish(f,
                        "Query", &__self_0),
                Phase::QueryPart(__self_0, __self_1) =>
                    ::core::fmt::Formatter::debug_tuple_field2_finish(f,
                        "QueryPart", __self_0, &__self_1),
                Phase::CheckpointWrite =>
                    ::core::fmt::Formatter::write_str(f, "CheckpointWrite"),
                Phase::Relation =>
                    ::core::fmt::Formatter::write_str(f, "Relation"),
                Phase::Final => ::core::fmt::Formatter::write_str(f, "Final"),
            }
        }
    }
    #[automatically_derived]
    #[doc(hidden)]
    unsafe impl ::core::clone::TrivialClone for Phase { }
    #[automatically_derived]
    impl ::core::clone::Clone for Phase {
        #[inline]
        fn clone(&self) -> Phase {
            let _: ::core::clone::AssertParamIsClone<u8>;
            let _: ::core::clone::AssertParamIsClone<usize>;
            *self
        }
    }
    #[automatically_derived]
    impl ::core::marker::Copy for Phase { }
    #[automatically_derived]
    impl ::core::marker::StructuralPartialEq for Phase { }
    #[automatically_derived]
    impl ::core::cmp::PartialEq for Phase {
        #[inline]
        fn eq(&self, other: &Phase) -> bool {
            let __self_discr = ::core::intrinsics::discriminant_value(self);
            let __arg1_discr = ::core::intrinsics::discriminant_value(other);
            __self_discr == __arg1_discr &&
                match (self, other) {
                    (Phase::SemanticPart(__self_0),
                        Phase::SemanticPart(__arg1_0)) => __self_0 == __arg1_0,
                    (Phase::Merkle(__self_0), Phase::Merkle(__arg1_0)) =>
                        __self_0 == __arg1_0,
                    (Phase::Query(__self_0), Phase::Query(__arg1_0)) =>
                        __self_0 == __arg1_0,
                    (Phase::QueryPart(__self_0, __self_1),
                        Phase::QueryPart(__arg1_0, __arg1_1)) =>
                        __self_1 == __arg1_1 && __self_0 == __arg1_0,
                    _ => true,
                }
        }
    }
    #[automatically_derived]
    impl ::core::cmp::Eq for Phase {
        #[inline]
        #[doc(hidden)]
        #[coverage(off)]
        fn assert_fields_are_eq(&self) {
            let _: ::core::cmp::AssertParamIsEq<u8>;
            let _: ::core::cmp::AssertParamIsEq<usize>;
        }
    }
    pub type Observer = Option<fn(Phase)>;
    fn mark(obs: Observer, p: Phase) { if let Some(f) = obs { f(p); } }
    pub fn checkpoint_size(v: Variant) -> usize {
        CHECKPOINT_FIXED + 16 * v.final_len()
    }
    pub struct View<'a> {
        pub variant: Variant,
        pub semantic: &'a [u8],
        pub y1: &'a [u8],
        pub inactive: E,
        pub round0: &'a [u8],
        pub folded_root: Option<&'a [u8; 32]>,
        pub round1: &'a [u8],
        pub final_message: &'a [u8],
        pub query_bytes: &'a [u8],
    }
    fn echeck(b: &[u8], k: bool) -> Result<(), Error> {
        for c in b.chunks_exact(32) {
            let x = E::from_le_bytes(c).ok_or(Error::Parse)?;
            if k && x.c1() != K::ZERO { return Err(Error::Parse); }
        }
        Ok(())
    }
    impl<'a> View<'a> {
        /// Length of the retired eight-way stored proof for `v` (124,343 bytes for
        /// S2). A layout figure only: the adopted stored length is `PROOF_BYTES`.
        pub fn eight_way_proof_bytes(v: Variant) -> usize {
            HEADER + SEMANTIC_BYTES + 29 * 32 + 32 + 7 * 32 +
                        if v.folds() == 2 { 32 + 7 * 32 } else { 0 } +
                    v.final_len() * 32 +
                22 *
                    (INITIAL_QUERY_BYTES +
                            if v.folds() == 2 { SECOND_QUERY_BYTES } else { 0 })
        }
    }
    pub struct Prepared {
        pub variant: Variant,
        pub roots: [[u8; 32]; 2],
        pub gamma: E,
        pub kappa: E,
        pub alpha: [E; 2],
        pub rho: K,
        pub queries: [u32; 22],
        pub semantic_alpha: [K; 10],
        pub z: [SecureCirclePoint; 2],
        pub claim: E,
        pub state: [u8; 32],
    }
    fn prepared_claim<H: Digest32>(sem: &crate::r1_semantic::Verified<H>,
        y1: &[u8], inactive: E, g: &[E; 29], kappa: E) -> Result<E, Error> {
        let k = powers::<7>(kappa);
        let mut parts = [E::ZERO; 7];
        parts[0] = inactive;
        for point in 0..6 {
            let mut dot = crate::fast_pairing::EbyKDot::new();
            for l in 0..29 {
                let scalar =
                    match point {
                        0..=2 => sem.claims[point][l],
                        3 => sem.extra[l],
                        4 => sem.before_z1[l],
                        _ => field(y1, l).c0(),
                    };
                dot.push(g[l], scalar).map_err(|_| Error::Parse)?;
            }
            parts[point + 1] = dot.finish();
        }
        let mut claim = E::ZERO;
        for i in 0..7 {
            crate::trace::value(14, i, parts[i]);
            claim = claim.add(k[i].mul(parts[i]));
        }
        crate::trace::value(14, 7, claim);
        Ok(claim)
    }
    impl Prepared {
        #[inline(never)]
        pub fn new<H: Digest32>(sem: &crate::r1_semantic::Verified<H>,
            v: &View<'_>, hash: H, g: &mut [E; 29])
            -> Result<Box<Self>, Error> {
            let mut t =
                Transcript::new(hash, sem.transcript.state(), v.variant);
            let gamma = t.scalar(27, v.y1, true);
            let kappa = t.scalar(28, &v.inactive.to_le_bytes(), false);
            let alpha0 = t.scalar(29, v.round0, false);
            let (alpha, row) =
                if v.variant.folds() == 2 {
                    let mut bytes = Vec::with_capacity(32 + 224);
                    bytes.extend_from_slice(v.folded_root.unwrap());
                    bytes.extend_from_slice(v.round1);
                    ([alpha0, t.scalar(30, &bytes, false)], 31)
                } else { ([alpha0, E::ZERO], 30) };
            let queries = t.queries(row, v.final_message)?;
            let rho = t.scalar_k(row + 1, &[]);
            *g = powers::<29>(gamma);
            let claim = prepared_claim(sem, v.y1, v.inactive, g, kappa)?;
            Ok(Box::new(Self {
                        variant: v.variant,
                        roots: sem.roots,
                        gamma,
                        kappa,
                        alpha,
                        rho,
                        queries,
                        semantic_alpha: sem.alpha,
                        z: sem.z,
                        claim,
                        state: t.state,
                    }))
        }
    }
    pub struct Accumulator {
        pub weights: Vec<K>,
        pub rhs: E,
        pub power: K,
        pub next: usize,
    }
    impl Accumulator {
        pub fn new(v: Variant) -> Result<Self, Error> {
            Ok(Self {
                    weights: aspis_core::r0::heap::filled(v.final_len(),
                                K::ZERO).map_err(|_| Error::Allocation)?,
                    rhs: E::ZERO,
                    power: K::ONE,
                    next: 0,
                })
        }
    }
    pub fn four_dots(q: &[u8], g: &[E; 29]) -> [E; 4] {
        core::array::from_fn(|s|
                {
                    let mut a = E::ZERO;
                    for l in 0..26 {
                        a =
                            a.add(g[l].mul_m31(M31::from_le_bytes(q[s * 120 +
                                                                l * 4..s * 120 + l * 4 + 4].try_into().unwrap()).unwrap()));
                    }
                    a =
                        a.add(g[28].mul_qm31(K::from_le_bytes(&q[s * 120 +
                                                        104..s * 120 + 120]).unwrap()));
                    for l in 0..2 {
                        a =
                            a.add(g[l +
                                            26].mul_qm31(K::from_le_bytes(&q[480 + s * 32 +
                                                            l * 16..480 + s * 32 + l * 16 + 16]).unwrap()));
                    }
                    a
                })
    }
    pub fn circle_fold(alpha: E, u: usize, a: [E; 4]) -> E {
        let p =
            crate::fast_domain::fibre_point(domain::FibreIndex::new(u).unwrap());
        let ix = p.x.inv();
        let iy = p.y.inv();
        let [a, b, c, d] = a;
        let h0 = a.add(b).add(c).add(d).mul_m31(QUARTER);
        let h1 = a.sub(b).sub(c).add(d).mul_m31(QUARTER.mul(iy));
        let h2 = a.add(b).sub(c).sub(d).mul_m31(QUARTER.mul(ix));
        let h3 = a.sub(b).add(c).sub(d).mul_m31(QUARTER.mul(ix).mul(iy));
        h0.add(alpha.mul(h1.add(alpha.mul(h2.add(alpha.mul(h3))))))
    }
    pub fn line_fold(alpha: E, v: usize, a: [E; 4]) -> E {
        let x =
            crate::fast_domain::line_node(domain::FibreIndex::new(4 *
                            v).unwrap());
        let y =
            crate::fast_domain::line_node(domain::FibreIndex::new(4 * v +
                            3).unwrap());
        let z = x.mul(x).double().sub(M31::ONE);
        let half = M31(1073741824);
        let [a, b, c, d] = a;
        let h0 = a.add(b).add(c).add(d).mul_m31(QUARTER);
        let h2 = a.add(b).sub(c).sub(d).mul_m31(QUARTER.mul(z.inv()));
        let c0 = a.sub(b).mul_m31(half.mul(x.inv()));
        let c1 = d.sub(c).mul_m31(half.mul(y.inv()));
        let h1 = c0.add(c1).mul_m31(half);
        let h3 = c0.sub(c1).mul_m31(half.mul(z.inv()));
        h0.add(alpha.mul(h1.add(alpha.mul(h2.add(alpha.mul(h3))))))
    }
    /// The five base-field denominators used to fold one sampled query: circle
    /// x/y, followed by line x/y/z. Their inverses are batch-computed once per
    /// transaction so each query avoids five independent field inversions.
    struct QueryGeometry {
        start: usize,
        inverses: Vec<[M31; 5]>,
        line_z: Vec<M31>,
    }
    #[inline(always)]
    fn batch_prefix_products(flat: &[M31]) -> (Vec<M31>, M31) {
        let mut prefixes = Vec::with_capacity(flat.len());
        let mut product = M31::ONE;
        let mut index = 0;
        while index < flat.len() {
            let value = flat[index];
            prefixes.push(product);
            product = product.mul(value);
            index += 1;
        }
        (prefixes, product)
    }
    impl QueryGeometry {
        fn for_range(queries: &[u32; 22], start: usize, end: usize)
            -> Result<Self, Error> {
            if start > end || end > queries.len() {
                return Err(Error::Query);
            }
            let mut line_z_values = Vec::with_capacity(end - start);
            let mut flat = Vec::with_capacity((end - start) * 5);
            for &query in &queries[start..end] {
                let u = query as usize;
                let fibre =
                    domain::FibreIndex::new(u).map_err(|_| Error::Query)?;
                let domain::Point { x: circle_x, y: circle_y } =
                    crate::fast_domain::fibre_point(fibre);
                let line_x =
                    crate::fast_domain::line_node(domain::FibreIndex::new(u / 4
                                        * 4).map_err(|_| Error::Query)?);
                let line_y =
                    crate::fast_domain::line_node(domain::FibreIndex::new(u / 4
                                            * 4 + 3).map_err(|_| Error::Query)?);
                let line_z = line_x.mul(line_x).double().sub(M31::ONE);
                let values = [circle_x, circle_y, line_x, line_y, line_z];
                if values.iter().any(|x| *x == M31::ZERO) {
                    return Err(Error::Query);
                }
                flat.extend_from_slice(&values);
                line_z_values.push(line_z);
            }
            if flat.is_empty() {
                return Ok(Self {
                            start,
                            inverses: Vec::new(),
                            line_z: line_z_values,
                        });
            }
            let (prefixes, product) = batch_prefix_products(&flat);
            let mut suffix_inverse = product.inv();
            let mut flat_inverse = Vec::with_capacity(flat.len());
            flat_inverse.resize(flat.len(), M31::ZERO);
            for i in (0..flat.len()).rev() {
                flat_inverse[i] = suffix_inverse.mul(prefixes[i]);
                suffix_inverse = suffix_inverse.mul(flat[i]);
            }
            let inverses =
                (0..line_z_values.len()).map(|i|
                            core::array::from_fn(|j|
                                    flat_inverse[5 * i + j])).collect();
            Ok(Self { start, inverses, line_z: line_z_values })
        }
        #[inline(always)]
        fn for_query(&self, index: usize) -> &[M31; 5] {
            &self.inverses[index - self.start]
        }
    }
    #[inline(always)]
    fn circle_fold_with_inverses(alpha: E, a: [E; 4], inverse: &[M31; 5])
        -> E {
        let [ix, iy, _, _, _] = *inverse;
        let [a, b, c, d] = a;
        let h0 = a.add(b).add(c).add(d).mul_m31(QUARTER);
        let h1 = a.sub(b).sub(c).add(d).mul_m31(QUARTER.mul(iy));
        let h2 = a.add(b).sub(c).sub(d).mul_m31(QUARTER.mul(ix));
        let h3 = a.sub(b).add(c).sub(d).mul_m31(QUARTER.mul(ix).mul(iy));
        h0.add(alpha.mul(h1.add(alpha.mul(h2.add(alpha.mul(h3))))))
    }
    #[inline(always)]
    fn line_fold_with_inverses(alpha: E, a: [E; 4], inverse: &[M31; 5]) -> E {
        let [_, _, ix, iy, iz] = *inverse;
        let half = M31(1073741824);
        let [a, b, c, d] = a;
        let h0 = a.add(b).add(c).add(d).mul_m31(QUARTER);
        let h2 = a.add(b).sub(c).sub(d).mul_m31(QUARTER.mul(iz));
        let c0 = a.sub(b).mul_m31(half.mul(ix));
        let c1 = d.sub(c).mul_m31(half.mul(iy));
        let h1 = c0.add(c1).mul_m31(half);
        let h3 = c0.sub(c1).mul_m31(half.mul(iz));
        h0.add(alpha.mul(h1.add(alpha.mul(h2.add(alpha.mul(h3))))))
    }
    /// Transaction-local residues. At a group boundary each limb is <2^34.
    /// Four products add at most 4*(P-1)^2; adding the retained folded residue
    /// still fits u64 because 4*(P-1)^2+2^34 < 2^64. Flush after each four queries.
    struct BatchedWeights {
        raw: Vec<[u64; 4]>,
        terms: usize,
    }
    impl BatchedWeights {
        fn new(weights: &[K]) -> Result<Self, Error> {
            let mut raw =
                aspis_core::r0::heap::filled(weights.len(),
                            [0u64; 4]).map_err(|_| Error::Allocation)?;
            let mut index = 0;
            while index < weights.len() {
                let w = weights[index];
                raw[index] =
                    [w.c0.a.0 as u64, w.c0.b.0 as u64, w.c1.a.0 as u64,
                            w.c1.b.0 as u64];
                index += 1;
            }
            Ok(Self { raw, terms: 0 })
        }
        #[inline(always)]
        fn push(&mut self, index: usize, power: K, basis: M31) {
            let flush = self.terms & 3 == 3;
            update_residue_row(&mut self.raw[index], power, basis, flush);
        }
        fn value(&self, index: usize) -> K {
            let [a, b, c, d] = self.raw[index].map(M31::reduce_u64);
            K {
                c0: aspis_core::field::CM31 { a, b },
                c1: aspis_core::field::CM31 { a: c, b: d },
            }
        }
        fn finish(&self, weights: &mut [K]) {
            for (i, w) in weights.iter_mut().enumerate() {
                *w = self.value(i);
            }
        }
    }
    #[inline(always)]
    fn residue_limb_at(row: &[u64; 4], index: usize) -> u64 { row[index] }
    #[inline(always)]
    fn power_limb_at(limbs: &[u32; 4], index: usize) -> u32 { limbs[index] }
    #[inline(always)]
    fn update_residue_row(row: &mut [u64; 4], power: K, basis: M31,
        flush: bool) {
        let limbs = [power.c0.a.0, power.c0.b.0, power.c1.a.0, power.c1.b.0];
        for j in 0..4 {
            let old = residue_limb_at(row, j);
            let limb = power_limb_at(&limbs, j);
            row[j] = old + u64::from(limb) * u64::from(basis.0);
        }
        if flush {
            for limb in row { *limb = (*limb & 0x7fff_ffff) + (*limb >> 31); }
        }
    }
    #[inline(never)]
    pub fn accumulate(p: &Prepared, a: &mut Accumulator, index: usize,
        value: E) {
        let mut node =
            crate::fast_domain::line_node(domain::FibreIndex::new(if p.variant.folds()
                                == 1 {
                            index
                        } else { index / 4 * 4 }).unwrap());
        if p.variant.folds() == 2 {
            for _ in 0..2 { node = node.mul(node).double().sub(M31::ONE); }
        }
        accumulate_with_node(p, a, node, value, None)
    }
    #[inline(never)]
    fn accumulate_with_node(p: &Prepared, a: &mut Accumulator, mut node: M31,
        value: E, mut pending: Option<&mut BatchedWeights>) {
        let mut basis = [M31::ZERO; 256];
        basis[0] = M31::ONE;
        let mut n = 1;
        while n < a.weights.len() {
            for j in 0..n { basis[n + j] = basis[j].mul(node); }
            node = node.mul(node).double().sub(M31::ONE);
            n *= 2;
        }
        for j in 0..a.weights.len() {
            if let Some(weights) = pending.as_deref_mut() {
                weights.push(j, a.power, basis[j]);
                { a.weights[j] = weights.value(j); }
            } else {
                a.weights[j] = a.weights[j].add(a.power.mul_m31(basis[j]));
            }
            crate::trace::value(12, a.next * a.weights.len() + j,
                E::from_qm31(a.weights[j]));
            crate::trace::value(13, a.next * a.weights.len() + j,
                E::from_m31(basis[j]));
        }
        if let Some(weights) = pending { weights.terms += 1; }
        a.rhs = a.rhs.add(value.mul_qm31(a.power));
        crate::trace::value(11, a.next, a.rhs);
        a.power = a.power.mul(p.rho);
        a.next += 1;
    }
    #[inline(always)]
    fn basis_at(basis: &[M31; 256], index: usize) -> M31 { basis[index] }
    #[inline(always)]
    fn accumulated_weight_at(weights: &[K], index: usize) -> K {
        weights[index]
    }
    #[inline(never)]
    fn accumulate_batched_with_node(p: &Prepared, a: &mut Accumulator,
        mut node: M31, value: E, weights: &mut BatchedWeights) {
        let width = a.weights.len();
        let mut basis = [M31::ZERO; 256];
        basis[0] = M31::ONE;
        let mut n = 1;
        while n < width {
            for j in 0..n { basis[n + j] = basis[j].mul(node); }
            node = node.mul(node).double().sub(M31::ONE);
            n *= 2;
        }
        for j in 0..width {
            weights.push(j, a.power, basis_at(&basis, j));
            { a.weights[j] = weights.value(j); }
            crate::trace::value(12, a.next * width + j,
                E::from_qm31(accumulated_weight_at(&a.weights, j)));
            crate::trace::value(13, a.next * width + j,
                E::from_m31(basis_at(&basis, j)));
        }
        weights.terms += 1;
        a.rhs = a.rhs.add(value.mul_qm31(a.power));
        crate::trace::value(11, a.next, a.rhs);
        a.power = a.power.mul(p.rho);
        a.next += 1;
    }
    pub fn polynomial(bytes: &[u8], x: E) -> E {
        (0..7).rev().fold(E::ZERO, |a, i| a.mul(x).add(field(bytes, i)))
    }
    fn finish_relation_round(poly: &[u8], alpha: E, mut claim: E,
        round: usize) -> Result<E, Error> {
        let lhs = field(poly, 0).add(field(poly, 4));
        let rhs = claim.mul_m31(QUARTER);
        crate::trace::value(15, 3 * round, lhs);
        crate::trace::value(15, 3 * round + 1, rhs);
        if lhs != rhs { return Err(Error::Relation); }
        claim = polynomial(poly, alpha);
        crate::trace::value(15, 3 * round + 2, claim);
        Ok(claim)
    }
    fn finish_query_dot(final_message: &[u8], weights: &[K])
        -> Result<E, Error> {
        let mut dot = crate::fast_pairing::EbyKDot::new();
        let mut j = 0;
        while j < weights.len() {
            dot.push(field(final_message, j),
                        weights[j]).map_err(|_| Error::Parse)?;
            j += 1;
        }
        Ok(dot.finish())
    }
    #[inline(never)]
    pub fn finish_relation(v: &View<'_>, p: &Prepared, a: &Accumulator,
        obs: Observer) -> Result<(), Error> {
        let mut claim = p.claim;
        claim = finish_relation_round(v.round0, p.alpha[0], claim, 0)?;
        if p.variant.folds() == 2 {
            claim = finish_relation_round(v.round1, p.alpha[1], claim, 1)?;
        }
        let weights = Weights::new(p.variant, &p.semantic_alpha, &p.z)?;
        let pair =
            weights.pair(&p.alpha[..p.variant.folds()], v.final_message,
                    p.kappa)?;
        crate::trace::value(16, 0, pair);
        crate::trace::value(16, 1, claim);
        if pair != claim { return Err(Error::Relation); }
        mark(obs, Phase::Relation);
        let actual = finish_query_dot(v.final_message, &a.weights)?;
        crate::trace::value(17, 0, actual);
        crate::trace::value(17, 1, a.rhs);
        if a.next != 22 || actual != a.rhs { return Err(Error::Query); }
        mark(obs, Phase::Final);
        Ok(())
    }
    fn put(out: &mut Vec<u8>, x: E) {
        out.extend_from_slice(&x.to_le_bytes());
    }
    fn put_k(out: &mut Vec<u8>, x: K) {
        let mut b = [0; 16];
        x.write_le_bytes(&mut b);
        out.extend_from_slice(&b);
    }
    pub fn checkpoint<H: Digest32>(p: &Prepared, a: &Accumulator,
        proof: &[u8], public: &[u8], hash: H) -> Vec<u8> {
        let mut out = Vec::with_capacity(checkpoint_size(p.variant));
        out.extend_from_slice(b"R1P2CKP2");
        out.extend_from_slice(&[p.variant.tag(), a.next as u8, 1, 0, 0, 0, 0,
                        0]);
        out.extend_from_slice(&hash.digest(&[proof]));
        out.extend_from_slice(&hash.digest(&[public]));
        out.extend_from_slice(&p.state);
        for root in &p.roots { out.extend_from_slice(root); }
        for x in [p.gamma, p.kappa, p.alpha[0], p.alpha[1]] {
            put(&mut out, x);
        }
        put_k(&mut out, p.rho);
        for q in p.queries { out.extend_from_slice(&q.to_le_bytes()); }
        for x in p.semantic_alpha {
            let mut b = [0; 16];
            x.write_le_bytes(&mut b);
            out.extend_from_slice(&b);
        }
        for z in p.z {
            for x in [z.x, z.y] {
                let mut b = [0; 16];
                x.write_le_bytes(&mut b);
                out.extend_from_slice(&b);
            }
        }
        for x in [p.claim, a.rhs] { put(&mut out, x); }
        put_k(&mut out, a.power);
        for &x in &a.weights { put_k(&mut out, x); }
        let sum = hash.digest(&[b"UNPROVED:R1:checkpoint", &out]);
        out.extend_from_slice(&sum);
        match (&out.len(), &checkpoint_size(p.variant)) {
            (left_val, right_val) => {
                if !(*left_val == *right_val) {
                    let kind = ::core::panicking::AssertKind::Eq;
                    ::core::panicking::assert_failed(kind, &*left_val,
                        &*right_val, ::core::option::Option::None);
                }
            }
        };
        out
    }
    struct Reader<'a> {
        bytes: &'a [u8],
        at: usize,
    }
    impl<'a> Reader<'a> {
        fn raw<const N : usize>(&mut self) -> [u8; N] {
            let b = self.bytes[self.at..self.at + N].try_into().unwrap();
            self.at += N;
            b
        }
        fn e(&mut self) -> Result<E, Error> {
            E::from_le_bytes(&self.raw::<32>()).ok_or(Error::Checkpoint)
        }
        #[inline(always)]
        fn k(&mut self) -> Result<K, Error> {
            K::from_le_bytes(&self.raw::<16>()).ok_or(Error::Checkpoint)
        }
    }
    #[inline(always)]
    fn validate_checkpoint_queries(queries: &[u32; 22]) -> Result<(), Error> {
        let mut i = 0;
        while i < queries.len() {
            let q = queries[i];
            if q >= 1 << 18 || queries[..i].contains(&q) {
                return Err(Error::Checkpoint);
            }
            i += 1;
        }
        Ok(())
    }
    #[inline(always)]
    fn read_checkpoint_weights(bytes: &[u8], mut at: usize,
        mut weights: Vec<K>) -> Result<(Vec<K>, usize), Error> {
        for out in &mut weights {
            let mut reader = Reader { bytes, at };
            let value = reader.k()?;
            at = reader.at;
            *out = value;
        }
        Ok((weights, at))
    }
    #[inline(always)]
    fn read_checkpoint_semantic_alpha(bytes: &[u8], at: usize)
        -> Result<([K; 10], usize), Error> {
        let mut r = Reader { bytes, at };
        let values =
            [r.k()?, r.k()?, r.k()?, r.k()?, r.k()?, r.k()?, r.k()?, r.k()?,
                    r.k()?, r.k()?];
        Ok((values, r.at))
    }
    #[inline(never)]
    pub fn resume<H: Digest32>(bytes: &[u8], proof: &[u8], public: &[u8],
        v: Variant, hash: H) -> Result<(Box<Prepared>, Accumulator), Error> {
        if bytes.len() != checkpoint_size(v) || &bytes[..8] != b"R1P2CKP2" ||
                            bytes[8] != v.tag() || bytes[9] > 22 || bytes[10] != 1 ||
                bytes[11..16].iter().any(|&b| b != 0) {
            return Err(Error::Checkpoint);
        }
        let end = bytes.len() - 32;
        if bytes[16..48] != hash.digest(&[proof]) ||
                    bytes[48..80] != hash.digest(&[public]) ||
                bytes[end..] !=
                    hash.digest(&[b"UNPROVED:R1:checkpoint", &bytes[..end]]) {
            return Err(Error::Checkpoint);
        }
        let mut r = Reader { bytes, at: 80 };
        let state = r.raw();
        let roots = [r.raw(), r.raw()];
        let gamma = r.e()?;
        let kappa = r.e()?;
        let alpha = [r.e()?, r.e()?];
        let rho = r.k()?;
        let queries =
            [u32::from_le_bytes(r.raw()), u32::from_le_bytes(r.raw()),
                    u32::from_le_bytes(r.raw()), u32::from_le_bytes(r.raw()),
                    u32::from_le_bytes(r.raw()), u32::from_le_bytes(r.raw()),
                    u32::from_le_bytes(r.raw()), u32::from_le_bytes(r.raw()),
                    u32::from_le_bytes(r.raw()), u32::from_le_bytes(r.raw()),
                    u32::from_le_bytes(r.raw()), u32::from_le_bytes(r.raw()),
                    u32::from_le_bytes(r.raw()), u32::from_le_bytes(r.raw()),
                    u32::from_le_bytes(r.raw()), u32::from_le_bytes(r.raw()),
                    u32::from_le_bytes(r.raw()), u32::from_le_bytes(r.raw()),
                    u32::from_le_bytes(r.raw()), u32::from_le_bytes(r.raw()),
                    u32::from_le_bytes(r.raw()), u32::from_le_bytes(r.raw())];
        validate_checkpoint_queries(&queries)?;
        let (semantic_alpha, at) =
            read_checkpoint_semantic_alpha(bytes, r.at)?;
        r.at = at;
        let z =
            [SecureCirclePoint { x: r.k()?, y: r.k()? },
                    SecureCirclePoint { x: r.k()?, y: r.k()? }];
        let claim = r.e()?;
        let rhs = r.e()?;
        let power = r.k()?;
        let weights =
            aspis_core::r0::heap::filled(v.final_len(),
                        K::ZERO).map_err(|_| Error::Allocation)?;
        let (weights, at) = read_checkpoint_weights(bytes, r.at, weights)?;
        if at != end { return Err(Error::Checkpoint); }
        Ok((Box::new(Prepared {
                        variant: v,
                        roots,
                        gamma,
                        kappa,
                        alpha,
                        rho,
                        queries,
                        semantic_alpha,
                        z,
                        claim,
                        state,
                    }),
                Accumulator { weights, rhs, power, next: bytes[9] as usize }))
    }
    #[path = "candidate.rs"]
    pub mod candidate {
        //! ADOPTED R1 VERIFIER (PREREG-PROOF-SIZE-2, 2026-10-19; prototype from the
        //! proof-size feasibility test). UNPROVED: PROOF-SIZE-OBLIGATIONS-20261019.
        //!
        //! Two-transaction verifier for the fixed-length compact binary-multiproof
        //! format (`crate::compact`), re-exported as `verifier::{tx1, tx2,
        //! tx2_authenticated, parse_shape}`. Child module of `verifier`, so it reuses
        //! the transcript, folding, accumulation, relation and checkpoint code
        //! unchanged. Differences from the retired eight-way path
        //! (`verifier::eight_way`, audit builds only), and nothing else:
        //! - the stored proof is the compact format; semantic rows 14..26 and `y1`
        //!   are expanded to their logical 32-byte form (zero high half) before any
        //!   parse or hash, so every Fiat-Shamir message keeps its byte definition;
        //! - C1, C2 and the folded tree are binary trees; authentication is one
        //!   multiproof per tree per transaction batch (queries 0..SPLIT in stage 1,
        //!   SPLIT..22 in stage 2), from fixed, zero-padded node slots;
        //! - the checkpoint hashes the compact stored bytes.
        use super::*;
        use crate::compact::{self, CodecError, OPENING, SLOT_NODES, SPLIT};
        use crate::multiproof::{self, Arity};
        use aspis_core::state_only_private_merkle::private_leaf_hash_with_digest;
        impl From<CodecError> for Error {
            fn from(_: CodecError) -> Self { Error::Parse }
        }
        #[inline(always)]
        fn opening(proof: &[u8], i: usize) -> &[u8] {
            let at = compact::OFF_OPENINGS + i * OPENING;
            &proof[at..at + OPENING]
        }
        #[inline(always)]
        fn slot(proof: &[u8], s: usize) -> &[u8] {
            &proof[compact::slot_offset(s)..compact::slot_offset(s + 1)]
        }
        /// Fixed length, magic, variant S2, zero header tail.
        #[inline(never)]
        pub fn parse_shape(proof: &[u8]) -> Result<Variant, Error> {
            if proof.len() != compact::PROOF_BYTES ||
                            &proof[..8] != compact::MAGIC ||
                        proof[8] != Variant::S2.tag() ||
                    proof[9..16].iter().any(|&x| x != 0) {
                return Err(Error::Parse);
            }
            Ok(Variant::S2)
        }
        /// The shipped strict scan for every field outside the semantic prefix
        /// (the semantic prefix is checked by `Prefix::parse` after expansion).
        #[inline(never)]
        fn canonical_scan(proof: &[u8]) -> Result<(), Error> {
            compact::check_values(&proof[compact::OFF_Y1..compact::OFF_INACTIVE])?;
            echeck(&proof[compact::OFF_INACTIVE..compact::OFF_INACTIVE + 32],
                    false)?;
            echeck(&proof[compact::OFF_ROUND0..compact::OFF_FOLDED_ROOT],
                    false)?;
            echeck(&proof[compact::OFF_ROUND1..compact::OFF_OPENINGS],
                    false)?;
            for i in 0..22 {
                let q = opening(proof, i);
                for s in 0..4 {
                    for l in 0..26 {
                        M31::from_le_bytes(q[s * 120 +
                                                        l *
                                                            4..s * 120 + l * 4 +
                                                        4].try_into().unwrap()).ok_or(Error::Parse)?;
                    }
                    K::from_le_bytes(&q[s * 120 +
                                                104..s * 120 + 120]).ok_or(Error::Parse)?;
                    for l in 0..2 {
                        K::from_le_bytes(&q[480 + s * 32 +
                                                    l * 16..480 + s * 32 + l * 16 + 16]).ok_or(Error::Parse)?;
                    }
                }
                echeck(&q[672..800], false)?;
            }
            Ok(())
        }
        /// View over the logical semantic/y1 buffers and the stored wide fields.
        fn wide_view<'a>(proof: &'a [u8], semantic: &'a [u8], y1: &'a [u8])
            -> Result<View<'a>, Error> {
            Ok(View {
                    variant: Variant::S2,
                    semantic,
                    y1,
                    inactive: E::from_le_bytes(&proof[compact::OFF_INACTIVE..compact::OFF_ROUND0]).ok_or(Error::Parse)?,
                    round0: &proof[compact::OFF_ROUND0..compact::OFF_FOLDED_ROOT],
                    folded_root: Some(proof[compact::OFF_FOLDED_ROOT..compact::OFF_ROUND1].try_into().unwrap()),
                    round1: &proof[compact::OFF_ROUND1..compact::OFF_FINAL],
                    final_message: &proof[compact::OFF_FINAL..compact::OFF_OPENINGS],
                    query_bytes: &[],
                })
        }
        #[inline(always)]
        fn batch_keys(queries: &[u32; 22], lo: usize, n: usize, tree: usize)
            -> [u64; multiproof::MAX_BATCH] {
            let mut keys = [0u64; multiproof::MAX_BATCH];
            for j in 0..n {
                let u = queries[lo + j];
                let index = if tree == 2 { u / 4 } else { u };
                keys[j] = (u64::from(index) << 8) | j as u64;
            }
            keys
        }
        #[inline(always)]
        fn sort_batch_keys(mut keys: [u64; multiproof::MAX_BATCH], n: usize)
            -> [u64; multiproof::MAX_BATCH] {
            for i in 1..n {
                let mut j = i;
                while j > 0 &&
                        batch_key_at(&keys, j - 1) > batch_key_at(&keys, j) {
                    keys.swap(j - 1, j);
                    j -= 1;
                }
            }
            keys
        }
        #[inline(always)]
        fn batch_leaf<H: Digest32>(hash: H, tree: usize, q: &[u8])
            -> [u8; 32] {
            match tree {
                0 => {
                    let salt: [u8; 32] = q[608..640].try_into().unwrap();
                    private_leaf_hash_with_digest(hash, merkle::C1_TAG,
                        &q[..480], &salt)
                }
                1 => {
                    let salt: [u8; 32] = q[640..672].try_into().unwrap();
                    private_leaf_hash_with_digest(hash, merkle::C2_TAG,
                        &q[480..608], &salt)
                }
                _ => {
                    let salt: [u8; 32] = q[800..832].try_into().unwrap();
                    private_leaf_hash_with_digest(hash, 0x72, &q[672..800],
                        &salt)
                }
            }
        }
        #[inline(always)]
        fn same_batch_leaf(values: &[[u8; 32]; multiproof::MAX_BATCH],
            index: usize, leaf: [u8; 32]) -> bool {
            values[index] == leaf
        }
        #[inline(always)]
        fn same_batch_index(values: &[u32; multiproof::MAX_BATCH],
            index: usize, expected: u32) -> bool {
            values[index] == expected
        }
        #[inline(always)]
        fn batch_key_at(keys: &[u64; multiproof::MAX_BATCH], index: usize)
            -> u64 {
            keys[index]
        }
        /// Verify the three multiproofs of one batch. Indices are sorted as u64
        /// keys (index << 8 | position) so leaf hashes are written once, in sorted
        /// order; equal folded indices must carry identical leaves and are merged.
        #[inline(never)]
        fn batch_merkle<H: Digest32>(proof: &[u8], p: &Prepared,
            folded_root: &[u8; 32], batch: usize, hash: H)
            -> Result<(), Error> {
            let [root0, root1] = p.roots;
            batch_merkle_values(proof, p.queries,
                [root0, root1, *folded_root], batch, hash)
        }
        #[inline(always)]
        fn batch_merkle_values<H: Digest32>(proof: &[u8], queries: [u32; 22],
            roots: [[u8; 32]; 3], batch: usize, hash: H)
            -> Result<(), Error> {
            let mut idx = [0u32; multiproof::MAX_BATCH];
            let mut val = [[0u8; 32]; multiproof::MAX_BATCH];
            let [root0, root1, root2] = roots;
            batch_tree(proof, queries, root0, batch, 0, &mut idx, &mut val,
                    hash)?;
            batch_tree(proof, queries, root1, batch, 1, &mut idx, &mut val,
                    hash)?;
            batch_tree(proof, queries, root2, batch, 2, &mut idx, &mut val,
                    hash)?;
            Ok(())
        }
        #[inline(always)]
        fn batch_tree<H: Digest32>(proof: &[u8], queries: [u32; 22],
            root: [u8; 32], batch: usize, tree: usize,
            idx: &mut [u32; multiproof::MAX_BATCH],
            val: &mut [[u8; 32]; multiproof::MAX_BATCH], hash: H)
            -> Result<(), Error> {
            let (lo, hi) = if batch == 0 { (0, SPLIT) } else { (SPLIT, 22) };
            let n = hi - lo;
            let s = 3 * batch + tree;
            let keys = sort_batch_keys(batch_keys(&queries, lo, n, tree), n);
            let mut d = 0;
            let mut key_position = 0;
            while key_position < n {
                let key = batch_key_at(&keys, key_position);
                key_position += 1;
                let index = (key >> 8) as u32;
                let q = opening(proof, lo + (key & 0xff) as usize);
                let leaf = batch_leaf(hash, tree, q);
                if d > 0 && same_batch_index(idx, d - 1, index) {
                    if !same_batch_leaf(val, d - 1, leaf) {
                        return Err(Error::Merkle);
                    }
                    continue;
                }
                idx[d] = index;
                val[d] = leaf;
                d += 1;
            }
            let count =
                multiproof::node_count(Arity::Two,
                            &idx[..d]).ok_or(Error::Merkle)?;
            let nodes = slot(proof, s);
            if count > SLOT_NODES[s] ||
                    nodes[32 *
                                        count..].chunks_exact(8).any(|w|
                            u64::from_le_bytes(w.try_into().unwrap()) != 0) {
                return Err(Error::Parse);
            }
            if !multiproof::verify_in_place(hash, Arity::Two, &root, idx, val,
                        d, &nodes[..32 * count]) {
                return Err(Error::Merkle);
            }
            Ok(())
        }
        /// The shipped per-query folding and accumulation, reading the candidate
        /// opening (C1/C2 values at the shipped offsets 0..608, folded values at
        /// 672..800). Merkle authentication was done per batch.
        #[inline(always)]
        fn query_values(proof: &[u8], p: &Prepared, mut a: Accumulator,
            g: &[E; 29], obs: Observer, geometry: &QueryGeometry,
            mut pending: BatchedWeights)
            -> Result<(Accumulator, BatchedWeights), Error> {
            let i = a.next;
            let u = p.queries[i] as usize;
            let q = opening(proof, i);
            let dots = crate::fast_dots::four_dots(q, g);
            crate::trace::value(9, 4 * i, dots[0]);
            crate::trace::value(9, 4 * i + 1, dots[1]);
            crate::trace::value(9, 4 * i + 2, dots[2]);
            crate::trace::value(9, 4 * i + 3, dots[3]);
            let inverse = *geometry.for_query(i);
            let folded =
                circle_fold_with_inverses(p.alpha[0], dots, &inverse);
            crate::trace::value(10, 2 * i, folded);
            let values = core::array::from_fn(|s| field(&q[672..800], s));
            if folded != values[u % 4] { return Err(Error::Query); }
            let folded =
                line_fold_with_inverses(p.alpha[1], values, &inverse);
            crate::trace::value(10, 2 * i + 1, folded);
            let z = geometry.line_z[i - geometry.start];
            let node = z.mul(z).double().sub(M31::ONE);
            accumulate_batched_with_node(p, &mut a, node, folded,
                &mut pending);
            mark(obs, Phase::Query(i));
            Ok((a, pending))
        }
        #[inline(always)]
        fn query_loop(proof: &[u8], p: &Prepared, mut a: Accumulator,
            g: &[E; 29], obs: Observer, geometry: &QueryGeometry,
            pending: BatchedWeights, end: usize)
            -> Result<(Accumulator, BatchedWeights), Error> {
            let mut state = Ok((a, pending));
            loop {
                match state {
                    Err(error) => return Err(error),
                    Ok((a, pending)) => {
                        if a.next >= end { return Ok((a, pending)); }
                        state =
                            query_values(proof, p, a, g, obs, geometry, pending);
                    }
                }
            }
        }
        #[inline(never)]
        fn prepare<H: Digest32>(public: Public<'_>, proof: &[u8], hash: H,
            obs: Observer, g: &mut [E; 29]) -> Result<Box<Prepared>, Error> {
            let mut logical =
                aspis_core::r0::heap::filled(compact::LOGICAL_SEMANTIC +
                                compact::LOGICAL_Y1, 0u8).map_err(|_| Error::Allocation)?;
            let (semantic, y1) =
                logical.split_at_mut(compact::LOGICAL_SEMANTIC);
            compact::expand_semantic(&proof[compact::OFF_SEMANTIC..compact::OFF_Y1],
                    semantic)?;
            compact::expand_values(&proof[compact::OFF_Y1..compact::OFF_INACTIVE],
                    y1)?;
            let v =
                wide_view(proof, &logical[..compact::LOGICAL_SEMANTIC],
                        &logical[compact::LOGICAL_SEMANTIC..])?;
            let sem =
                crate::r1_semantic::verify_observed(public, v.semantic, hash,
                            obs).map_err(|_| Error::Semantic)?;
            mark(obs, Phase::Semantic);
            Prepared::new(&sem, &v, hash, g)
        }
        /// Stage 1: strict parse of the whole stored proof, semantic layer,
        /// challenges, batch-A multiproofs and queries 0..SPLIT; returns the
        /// checkpoint over the compact stored bytes.
        #[inline(never)]
        pub fn tx1<H: Digest32>(public: Public<'_>, public_bytes: &[u8],
            proof: &[u8], k: usize, hash: H, obs: Observer)
            -> Result<Vec<u8>, Error> {
            if k != SPLIT { return Err(Error::Parse); }
            parse_shape(proof)?;
            canonical_scan(proof)?;
            mark(obs, Phase::Parsed);
            let mut g = [E::ZERO; 29];
            let p = prepare(public, proof, hash, obs, &mut g)?;
            let a = Accumulator::new(Variant::S2)?;
            mark(obs, Phase::Prepare);
            let folded_root: [u8; 32] =
                proof[compact::OFF_FOLDED_ROOT..compact::OFF_ROUND1].try_into().unwrap();
            batch_merkle(proof, &p, &folded_root, 0, hash)?;
            mark(obs, Phase::Merkle(0));
            let geometry = QueryGeometry::for_range(&p.queries, 0, k)?;
            let pending = BatchedWeights::new(&a.weights)?;
            let (mut a, pending) =
                query_loop(proof, &p, a, &g, obs, &geometry, pending, k)?;
            pending.finish(&mut a.weights);
            let bytes = checkpoint(&p, &a, proof, public_bytes, hash);
            mark(obs, Phase::CheckpointWrite);
            Ok(bytes)
        }
        #[inline(never)]
        fn tx2_common<H: Digest32>(public_bytes: &[u8], proof: &[u8],
            checkpoint: &[u8], hash: H, obs: Observer) -> Result<(), Error> {
            let (p, a) =
                resume(checkpoint, proof, public_bytes, Variant::S2, hash)?;
            if a.next != SPLIT { return Err(Error::Checkpoint); }
            let g = powers::<29>(p.gamma);
            mark(obs, Phase::CheckpointRead);
            let inactive =
                E::from_le_bytes(&proof[compact::OFF_INACTIVE..compact::OFF_ROUND0]).ok_or(Error::Parse)?;
            let folded_root: [u8; 32] =
                proof[compact::OFF_FOLDED_ROOT..compact::OFF_ROUND1].try_into().unwrap();
            batch_merkle(proof, &p, &folded_root, 1, hash)?;
            mark(obs, Phase::Merkle(SPLIT));
            let geometry = QueryGeometry::for_range(&p.queries, a.next, 22)?;
            let pending = BatchedWeights::new(&a.weights)?;
            let (a, pending) =
                query_loop(proof, &p, a, &g, obs, &geometry, pending, 22)?;
            let Accumulator { mut weights, rhs, power, next } = a;
            pending.finish(&mut weights);
            let a = Accumulator { weights, rhs, power, next };
            let v =
                View {
                    variant: Variant::S2,
                    semantic: &[],
                    y1: &[],
                    inactive,
                    round0: &proof[compact::OFF_ROUND0..compact::OFF_FOLDED_ROOT],
                    folded_root: None,
                    round1: &proof[compact::OFF_ROUND1..compact::OFF_FINAL],
                    final_message: &proof[compact::OFF_FINAL..compact::OFF_OPENINGS],
                    query_bytes: &[],
                };
            finish_relation(&v, &p, &a, obs)
        }
        /// Stage 2 with checkpoint provenance established by the caller (Pool
        /// route); same precondition as the shipped `tx2_authenticated`.
        #[inline(never)]
        pub fn tx2_authenticated<H: Digest32>(public_bytes: &[u8],
            proof: &[u8], checkpoint: &[u8], hash: H, obs: Observer)
            -> Result<(), Error> {
            parse_shape(proof)?;
            mark(obs, Phase::Parsed);
            tx2_common(public_bytes, proof, checkpoint, hash, obs)
        }
        /// Stage 2 repeating the full canonical scan.
        #[inline(never)]
        pub fn tx2<H: Digest32>(public_bytes: &[u8], proof: &[u8],
            checkpoint: &[u8], hash: H, obs: Observer) -> Result<(), Error> {
            parse_shape(proof)?;
            canonical_scan(proof)?;
            mark(obs, Phase::Parsed);
            tx2_common(public_bytes, proof, checkpoint, hash, obs)
        }
    }
    pub use candidate::{parse_shape, tx1, tx2, tx2_authenticated};
    /// The one stored proof length of the adopted format (57,607 bytes).
    pub const PROOF_BYTES: usize = crate::compact::PROOF_BYTES;
    /// The one stage-1 split of the adopted format (queries 0..10 in stage 1).
    pub const SPLIT: usize = crate::compact::SPLIT;
    const _: () =
        if !(PROOF_BYTES == 57_607 && SPLIT == 10) {
            ::core::panicking::panic("assertion failed: PROOF_BYTES == 57_607 && SPLIT == 10")
        };
}
pub mod prover {
    //! UNPROVED COST PROBE. Own native prover, including D14 content.
    use alloc::{vec, vec::Vec};
    use aspis_core::{
        digest::LegacyHashFn, HashFn,
        field::{WideExact as E, M31, QM31 as K, CM31},
        r0::{
            self, CodeField, domain::{Point, FibreIndex},
            merkle, wire::FibreOpening, Message,
        },
        state_only_hiding::StateOnlyHidingContext,
    };
    use aspis_statement::pool_v1::{
        pair_forest_semantic_terminal::r0::Public,
        pair_forest_trace::PoolV1PairForestMergedC1CompilationV1,
    };
    use crate::host_forest::pool_v1_pair_forest_copy_active_row_masks_v1;
    use aspis_prover::{
        state_only_entropy::{
            StateOnlyAttemptSecrets, ReservedStateOnlyAttemptSecrets,
            DurableStateOnlyMaskNonceStore,
        },
        state_only_hiding::{
            apply_pool_v1_pair_forest_mask_material_v1,
            InMemoryStateOnlyMaskNonceStore, StateOnlyMaskBuildError,
            StateOnlyMaskNonceStore,
        },
    };
    use crate::{
        transport::Variant, verifier::Error,
        host_weights::{Weights, QUARTER, PERM},
        host_transcript::Transcript,
        host_commitment::{
            Commitment, CommitmentTime, EncodingDomain, PrivateSalts,
        },
        host_semantic::{BuiltSemantics, Commitments},
        r1_wire::Error as SError,
    };
    /// Host commitment backend. Adopted format (PREREG-PROOF-SIZE-2): salted
    /// leaves under binary trees; there is no unsalted or eight-way commitment.
    pub struct Backend {
        pub hash: HashFn,
        pub variant: Variant,
        pub domain: EncodingDomain,
        pub messages: Vec<Message<E>>,
        pub c1: Option<Commitment>,
        pub c2: Option<Commitment>,
        c1_salts: Option<crate::host_commitment::PrivateSalts>,
        c2_salts: Option<crate::host_commitment::PrivateSalts>,
    }
    impl Commitments for Backend {
        fn c1(&mut self, columns: &[Vec<M31>; 26], d: &[K; 1024])
            -> Result<[u8; 32], SError> {
            let mut lane = 0;
            while lane < 26 {
                let mut row = 0;
                while row < 1024 {
                    self.messages[lane][row] = E::from_m31(columns[lane][row]);
                    row += 1;
                }
                lane += 1;
            }
            let mut row = 0;
            while row < 1024 {
                self.messages[28][row] = E::from_qm31(d[row]);
                row += 1;
            }
            let salts = self.c1_salts.take().ok_or(SError::Public)?;
            let c =
                Commitment::new_salted(self.hash, &self.domain,
                            CommitmentTime::C1, &self.messages, self.variant,
                            salts).map_err(|_| SError::Public)?;
            let root = c.root();
            self.c1 = Some(c);
            Ok(root)
        }
        fn c2(&mut self, h1: &[K], g: &[K; 1024])
            -> Result<[u8; 32], SError> {
            let mut row = 0;
            while row < 1024 {
                self.messages[26][row] = E::from_qm31(h1[row]);
                row += 1;
            }
            row = 0;
            while row < 1024 {
                self.messages[27][row] = E::from_qm31(g[row]);
                row += 1;
            }
            let salts = self.c2_salts.take().ok_or(SError::Public)?;
            let c =
                Commitment::new_salted(self.hash, &self.domain,
                            CommitmentTime::C2, &self.messages, self.variant,
                            salts).map_err(|_| SError::Public)?;
            let root = c.root();
            self.c2 = Some(c);
            Ok(root)
        }
    }
    pub fn round(q: &[E], w: &[E]) -> [E; 7] {
        match (&q.len(), &w.len()) {
            (left_val, right_val) => {
                if !(*left_val == *right_val) {
                    let kind = ::core::panicking::AssertKind::Eq;
                    ::core::panicking::assert_failed(kind, &*left_val,
                        &*right_val, ::core::option::Option::None);
                }
            }
        };
        let mut c = [E::ZERO; 7];
        let mut d = 0;
        while d < q.len() / 4 {
            let mut s = 0;
            while s < 4 {
                let mut t = 0;
                while t < 4 {
                    let at = s + PERM[t];
                    c[at] = c[at].add(q[4 * d + s].mul(w[4 * d + t]));
                    t += 1;
                }
                s += 1;
            }
            d += 1;
        }
        let mut i = 0;
        while i < 7 { c[i] = c[i].mul_m31(QUARTER); i += 1; }
        c
    }
    pub fn fold(q: &[E], alpha: E, dual: bool) -> Vec<E> {
        let mut out = Vec::with_capacity(q.len() / 4);
        let mut i = 0;
        while i < q.len() / 4 {
            let h = [q[4 * i], q[4 * i + 1], q[4 * i + 2], q[4 * i + 3]];
            let value = fold_cell(h, alpha, dual);
            out.push(value);
            i += 1;
        }
        out
    }
    #[inline(always)]
    fn fold_cell(h: [E; 4], alpha: E, dual: bool) -> E {
        if dual {
            h[0].add(alpha.mul(h[3].add(alpha.mul(h[2].add(alpha.mul(h[1])))))).mul_m31(QUARTER)
        } else {
            h[0].add(alpha.mul(h[1].add(alpha.mul(h[2].add(alpha.mul(h[3]))))))
        }
    }
    /// Ordered byte assembly used by the real pipeline; each field encoding is a leaf.
    fn encoded_slice(values: &[E]) -> Vec<u8> {
        let mut out = Vec::with_capacity(32 * values.len());
        let mut i = 0;
        while i < values.len() {
            out.extend_from_slice(&values[i].to_le_bytes());
            i += 1;
        }
        out
    }
    pub fn encoded(values: impl IntoIterator<Item = E>) -> Vec<u8> {
        values.into_iter().flat_map(E::to_le_bytes).collect()
    }
    /// Deterministic fixture-only rejection sampling of K limbs. No distribution
    /// property is inferred from these fixed test samples.
    fn tail_samples(hash: HashFn, seed: &[u8; 32]) -> [K; 56] {
        let mut counter = 0u64;
        let mut limb =
            ||
                loop {
                    let b =
                        hash(&[b"UNPROVED:R1:P2:fixture-tail", seed,
                                        &counter.to_le_bytes()]);
                    counter += 1;
                    let x =
                        u32::from_le_bytes(b[..4].try_into().unwrap()) & 0x7fffffff;
                    if x < aspis_core::field::P { break M31(x); }
                };
        core::array::from_fn(|_|
                K {
                    c0: CM31::new(limb(), limb()),
                    c1: CM31::new(limb(), limb()),
                })
    }
    /// Convenience API, deliberately fixture-only: it always emits a fully masked
    /// P3 proof in the adopted compact binary-multiproof format.
    pub fn prove(public: Public<'_>,
        compiled: &PoolV1PairForestMergedC1CompilationV1, variant: Variant,
        hash: HashFn, seed: &[u8; 32]) -> Result<Vec<u8>, Error> {
        prove_masked_fixture(public, compiled, variant, hash,
                seed).map(|(proof, _)| proof)
    }
    /// Checks describing the fixture mask constraints exercised before proving.
    pub struct MaskedFixtureAudit {
        pub c1_columns_inactive_balanced: usize,
        pub mask_only_columns_inactive_balanced: usize,
        pub d_inactive_balanced: bool,
        pub g_inactive_balanced: bool,
        pub h1_padding_inactive_balanced: bool,
        pub h1_total_balanced: bool,
    }
    #[automatically_derived]
    #[doc(hidden)]
    unsafe impl ::core::clone::TrivialClone for MaskedFixtureAudit { }
    #[automatically_derived]
    impl ::core::clone::Clone for MaskedFixtureAudit {
        #[inline]
        fn clone(&self) -> MaskedFixtureAudit {
            let _: ::core::clone::AssertParamIsClone<usize>;
            let _: ::core::clone::AssertParamIsClone<bool>;
            *self
        }
    }
    #[automatically_derived]
    impl ::core::marker::Copy for MaskedFixtureAudit { }
    #[automatically_derived]
    impl ::core::fmt::Debug for MaskedFixtureAudit {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            let names: &'static _ =
                &["c1_columns_inactive_balanced",
                            "mask_only_columns_inactive_balanced",
                            "d_inactive_balanced", "g_inactive_balanced",
                            "h1_padding_inactive_balanced", "h1_total_balanced"];
            let values: &[&dyn ::core::fmt::Debug] =
                &[&self.c1_columns_inactive_balanced,
                            &self.mask_only_columns_inactive_balanced,
                            &self.d_inactive_balanced, &self.g_inactive_balanced,
                            &self.h1_padding_inactive_balanced,
                            &&self.h1_total_balanced];
            ::core::fmt::Formatter::debug_struct_fields_finish(f,
                "MaskedFixtureAudit", names, values)
        }
    }
    #[automatically_derived]
    impl ::core::marker::StructuralPartialEq for MaskedFixtureAudit { }
    #[automatically_derived]
    impl ::core::cmp::PartialEq for MaskedFixtureAudit {
        #[inline]
        fn eq(&self, other: &MaskedFixtureAudit) -> bool {
            self.d_inactive_balanced == other.d_inactive_balanced &&
                                self.g_inactive_balanced == other.g_inactive_balanced &&
                            self.h1_padding_inactive_balanced ==
                                other.h1_padding_inactive_balanced &&
                        self.h1_total_balanced == other.h1_total_balanced &&
                    self.c1_columns_inactive_balanced ==
                        other.c1_columns_inactive_balanced &&
                self.mask_only_columns_inactive_balanced ==
                    other.mask_only_columns_inactive_balanced
        }
    }
    #[automatically_derived]
    impl ::core::cmp::Eq for MaskedFixtureAudit {
        #[inline]
        #[doc(hidden)]
        #[coverage(off)]
        fn assert_fields_are_eq(&self) {
            let _: ::core::cmp::AssertParamIsEq<usize>;
            let _: ::core::cmp::AssertParamIsEq<bool>;
        }
    }
    fn fixture_secret(hash: HashFn, domain: &[u8], seed: &[u8; 32],
        public: &[u8], variant: Variant) -> Result<[u8; 32], Error> {
        let mut value = hash(&[domain, seed, public, &[variant.tag()]]);
        if value == [0; 32] { return Err(Error::Semantic); }
        Ok(value)
    }
    fn inactive_sum_m31(values: &[M31], masks: &[u16; 64]) -> M31 {
        let mut sum = M31::ZERO;
        let mut row = 0;
        while row < values.len() {
            if masks[row >> 4] & (1 << (row & 15)) == 0 {
                sum = sum.add(values[row]);
            }
            row += 1;
        }
        sum
    }
    fn inactive_sum_k(values: &[K], masks: &[u16; 64]) -> K {
        let mut sum = K::ZERO;
        let mut row = 0;
        while row < values.len() {
            if masks[row >> 4] & (1 << (row & 15)) == 0 {
                sum = sum.add(values[row]);
            }
            row += 1;
        }
        sum
    }
    /// Deterministic, insecure masked fixture path. Its derivations exist only for
    /// reproducible local cost experiments and are not production entropy.
    pub fn prove_masked_fixture(public: Public<'_>,
        compiled: &PoolV1PairForestMergedC1CompilationV1, variant: Variant,
        hash: HashFn, fixture_seed: &[u8; 32])
        -> Result<(Vec<u8>, MaskedFixtureAudit), Error> {
        let public_bytes =
            crate::host_public::materialize_public_bytes(public).map_err(|_|
                        Error::Semantic)?;
        let context =
            StateOnlyHidingContext::pool_v1_pair_forest_v1(hash(&[&public_bytes]),
                fixture_secret(hash, b"UNPROVED:R1:fixture-mask-nonce",
                        fixture_seed, &public_bytes, variant)?);
        let binding =
            hash(&[b"UNPROVED:R1:P3:PRIVATE-ATTEMPT", &public_bytes,
                            &[variant.tag()], &context.encode()]);
        let attempt =
            StateOnlyAttemptSecrets::deterministic_spend_fixture(context.mask_nonce,
                fixture_secret(hash, b"UNPROVED:R1:fixture-field-entropy",
                        fixture_seed, &public_bytes, variant)?,
                fixture_secret(hash, b"UNPROVED:R1:fixture-leaf-seed",
                        fixture_seed, &public_bytes, variant)?);
        let mut nonce_store = InMemoryStateOnlyMaskNonceStore::default();
        prove_masked_with_attempt(public, compiled, variant, hash, context,
            binding, attempt, &mut nonce_store)
    }
    /// Secure-source P3 host API. Callers must supply OS-generated attempt
    /// secrets and a durable nonce ledger; successful reservations happen before
    /// mask derivation and leaf-salt derivation. This is still an UNPROVED
    /// protocol: fresh entropy alone does not establish zero knowledge.
    pub fn prove_masked_attempt(public: Public<'_>,
        compiled: &PoolV1PairForestMergedC1CompilationV1, variant: Variant,
        hash: HashFn, attempt: StateOnlyAttemptSecrets,
        nonce_store: &mut DurableStateOnlyMaskNonceStore)
        -> Result<(Vec<u8>, MaskedFixtureAudit), Error> {
        let public_bytes =
            crate::host_public::materialize_public_bytes(public).map_err(|_|
                        Error::Semantic)?;
        let context =
            StateOnlyHidingContext::pool_v1_pair_forest_v1(hash(&[&public_bytes]),
                attempt.mask_nonce());
        let binding =
            hash(&[b"UNPROVED:R1:P3:PRIVATE-ATTEMPT", &public_bytes,
                            &[variant.tag()], &context.encode()]);
        prove_masked_with_attempt(public, compiled, variant, hash, context,
            binding, attempt, nonce_store)
    }
    fn prove_masked_with_attempt(public: Public<'_>,
        compiled: &PoolV1PairForestMergedC1CompilationV1, variant: Variant,
        hash: HashFn, context: StateOnlyHidingContext, binding: [u8; 32],
        attempt: StateOnlyAttemptSecrets,
        nonce_store: &mut impl StateOnlyMaskNonceStore)
        -> Result<(Vec<u8>, MaskedFixtureAudit), Error> {
        let (reserved, material) =
            attempt.reserve_and_build_pool_v1_pair_forest_mask_material_v1(hash,
                        binding, context, nonce_store).map_err(mask_error)?;
        let mut noised_c1 = compiled.semantic_c1.clone();
        let applied =
            apply_pool_v1_pair_forest_mask_material_v1(&mut noised_c1,
                        material).map_err(|_| Error::Semantic)?;
        let masks =
            pool_v1_pair_forest_copy_active_row_masks_v1().map_err(|_|
                        Error::Semantic)?;
        let d: [K; 1024] =
            reserved.derive_pool_v1_pair_forest_zero_factor_d(hash,
                                    context).map_err(mask_error)?.try_into().map_err(|_|
                        Error::Semantic)?;
        if applied.g.len() != 1024 || applied.h1_padding.len() != 1024 {
            return Err(Error::Semantic);
        }
        let g = fixed_k_column(&applied.g);
        let h1_padding = fixed_k_column(&applied.h1_padding);
        let audit =
            audit_masks(&noised_c1.c1, &applied.mask_only_c1, &d, &g,
                &h1_padding, &masks);
        if audit.c1_columns_inactive_balanced != 16 ||
                            audit.mask_only_columns_inactive_balanced != 10 ||
                        !audit.d_inactive_balanced || !audit.g_inactive_balanced ||
                !audit.h1_padding_inactive_balanced {
            return Err(Error::Semantic);
        }
        let (c1_salts, c2_salts) =
            (Some(derive_private_salts(&reserved, context, hash,
                            merkle::C1_TAG)?),
                Some(derive_private_salts(&reserved, context, hash,
                            merkle::C2_TAG)?));
        let mut backend =
            Backend {
                hash,
                variant,
                domain: EncodingDomain::new().map_err(|_| Error::Allocation)?,
                messages: ::alloc::vec::from_elem([E::ZERO; 1024], 29),
                c1: None,
                c2: None,
                c1_salts,
                c2_salts,
            };
        let sem =
            crate::host_semantic::build_with_material(public, compiled,
                        &noised_c1, &applied.mask_only_c1, &d, &g, &h1_padding,
                        &mut backend, LegacyHashFn(hash),
                        variant).map_err(semantic_error)?;
        let h1_total_balanced =
            crate::prover_helper_sum::state_only_copy_helper_sum(&sem.columns[26])
                == Some(K::ZERO);
        if !h1_total_balanced { return Err(Error::Semantic); }
        let audit = MaskedFixtureAudit { h1_total_balanced, ..audit };
        let proof =
            prove_from_semantics(public, variant, hash, backend, sem,
                    (&reserved, context))?;
        Ok((proof, audit))
    }
    /// Fixed-size copy with no closure retaining a material-owner loan.
    fn fixed_k_column(values: &[K]) -> [K; 1024] {
        let mut out = [K::ZERO; 1024];
        let mut i = 0;
        while i < 1024 { out[i] = values[i]; i += 1; }
        out
    }
    fn audit_masks(c1: &[Vec<M31>], mask_only: &[Vec<M31>; 10], d: &[K; 1024],
        g: &[K; 1024], h1_padding: &[K; 1024], masks: &[u16; 64])
        -> MaskedFixtureAudit {
        let mut c1_columns_inactive_balanced = 0;
        let mut column = 0;
        while column < c1.len() {
            if inactive_sum_m31(&c1[column], masks) == M31::ZERO {
                c1_columns_inactive_balanced += 1;
            }
            column += 1;
        }
        let mut mask_only_columns_inactive_balanced = 0;
        column = 0;
        while column < 10 {
            if inactive_sum_m31(&mask_only[column], masks) == M31::ZERO {
                mask_only_columns_inactive_balanced += 1;
            }
            column += 1;
        }
        MaskedFixtureAudit {
            c1_columns_inactive_balanced,
            mask_only_columns_inactive_balanced,
            d_inactive_balanced: inactive_sum_k(d, masks) == K::ZERO,
            g_inactive_balanced: inactive_sum_k(g, masks) == K::ZERO,
            h1_padding_inactive_balanced: inactive_sum_k(h1_padding, masks) ==
                K::ZERO,
            h1_total_balanced: true,
        }
    }
    /// LOG D73.4.2: Lean `realGameP` rejects an attempt whose mask decode is
    /// exhausted (`exh`, R1Z/GamesR1P.lean:164, 184) and moves to the next one.
    /// With the retry loop, `MaskSampleExhausted` from either expander is
    /// therefore a rejected attempt; every other mask error still aborts. Without
    /// the loop (`r1p-check` off) behaviour is unchanged.
    fn mask_error(e: StateOnlyMaskBuildError) -> Error {
        if e == StateOnlyMaskBuildError::MaskSampleExhausted {
            return Error::Rejected;
        }
        let _ = e;
        Error::Semantic
    }
    /// LOG D73.4.1: a LogUp pole (Lean `¬ VR1`, R1Z/MaskImageVR1.lean:29) is a
    /// rejected attempt. The pole carries no detail; it becomes the same
    /// `Error::Rejected` as a failed P_R1 check.
    fn semantic_error(e: SError) -> Error {
        if e == SError::ActivePole { return Error::Rejected; }
        let _ = e;
        Error::Semantic
    }
    fn derive_private_salts(reserved: &ReservedStateOnlyAttemptSecrets,
        context: StateOnlyHidingContext, hash: HashFn, tag: u8)
        -> Result<PrivateSalts, Error> {
        let count = aspis_core::r0::FIBRE_COUNT;
        let mut salts = Vec::new();
        salts.try_reserve_exact(aspis_core::r0::FIBRE_COUNT).map_err(|_|
                    Error::Allocation)?;
        let mut result = Ok(salts);
        let mut index = 0usize;
        while index < count {
            result =
                match result {
                    Ok(salts) =>
                        derive_private_salt_step(reserved, context, hash, tag,
                            index as u32, salts),
                    Err(error) => Err(error),
                };
            index += 1;
        }
        result.map(PrivateSalts::new)
    }
    /// The R1 proof (PREREG-PROOF-SIZE-2, adopted 2026-10-19): binary trees (C1/C2
    /// built by the Backend, the padded folded tree here) and the fixed-length
    /// compact stored format of `crate::compact` (57,607 bytes). Every transcript
    /// message is the logical byte string of the retired eight-way format; only
    /// the roots (binary trees) and the stored encoding differ. R1 is variant S2.
    /// Owned result of rows 27–29. No transcript loan or iterator survives a phase.
    struct PreparedOpening {
        backend: Backend,
        sem: BuiltSemantics<LegacyHashFn>,
        transcript: Transcript<LegacyHashFn>,
        y1: Vec<u8>,
        gamma: E,
        inactive: E,
        kappa: E,
        alpha0: E,
        c0bytes: Vec<u8>,
        q1: Vec<E>,
        w1: Vec<E>,
        folded_word: Vec<E>,
    }
    #[inline(never)]
    pub(crate) fn retain_weights_box(w: Weights)
        -> alloc::boxed::Box<Weights> {
        const _: () =
            {
                if !(core::mem::size_of::<Weights>() ==
                            core::mem::size_of::<crate::weights::Weights>()) {
                    ::core::panicking::panic("assertion failed: core::mem::size_of::<Weights>() ==\n    core::mem::size_of::<crate::weights::Weights>()")
                };
                if !(core::mem::align_of::<Weights>() ==
                            core::mem::align_of::<crate::weights::Weights>()) {
                    ::core::panicking::panic("assertion failed: core::mem::align_of::<Weights>() ==\n    core::mem::align_of::<crate::weights::Weights>()")
                };
            };
        alloc::boxed::Box::new(w)
    }
    fn prepare_opening(variant: Variant, hash: HashFn, backend: Backend,
        sem: BuiltSemantics<LegacyHashFn>) -> Result<PreparedOpening, Error> {
        if variant != Variant::S2 { return Err(Error::Semantic); }
        let coefficients = opening_coefficients(variant, &backend.messages);
        let z1 =
            Point {
                x: E::from_qm31(sem.z[1].x),
                y: E::from_qm31(sem.z[1].y),
            };
        let y1 = opening_claim_bytes(&coefficients, z1);
        let mut transcript =
            Transcript::new(LegacyHashFn(hash), sem.transcript.state(),
                variant);
        let gamma = transcript.scalar(27, &y1, true);
        let q = opening_batch(&coefficients, gamma);
        let w =
            retain_weights_box(Weights::new(variant, &sem.alpha, &sem.z)?);
        let inactive = opening_inactive(&q, &w);
        let kappa = transcript.scalar(28, &inactive.to_le_bytes(), false);
        let mut weights =
            match aspis_core::r0::heap::filled(1024, E::ZERO) {
                Ok(v) => v,
                Err(_) => return Err(Error::Allocation),
            };
        w.materialize(kappa, weights.as_mut_slice().try_into().unwrap())?;
        let c0 = round(&q, &weights);
        let c0bytes = encoded_slice(&c0);
        let alpha0 = transcript.scalar(29, &c0bytes, false);
        let q1 = fold(&q, alpha0, false);
        let w1 = fold(&weights, alpha0, true);
        let folded_word =
            backend.domain.evaluate(&q1, 0).map_err(|_| Error::Allocation)?;
        Ok(PreparedOpening {
                backend,
                sem,
                transcript,
                y1,
                gamma,
                inactive,
                kappa,
                alpha0,
                c0bytes,
                q1,
                w1,
                folded_word,
            })
    }
    /// Coefficient permutation is a small unchanged leaf; the vector owner is here.
    fn opening_coefficients(variant: Variant, messages: &[Message<E>])
        -> Vec<Message<E>> {
        let mut coefficients = Vec::with_capacity(messages.len());
        let mut lane = 0;
        while lane < messages.len() {
            let column = variant.coefficients(&messages[lane]);
            coefficients.push(column);
            lane += 1;
        }
        coefficients
    }
    fn opening_claim_bytes(coefficients: &[Message<E>], z1: Point<E>)
        -> Vec<u8> {
        let mut bytes = Vec::with_capacity(32 * coefficients.len());
        let mut lane = 0;
        while lane < coefficients.len() {
            let value = r0::encoder::eval_message(&coefficients[lane], z1);
            bytes.extend_from_slice(&value.to_le_bytes());
            lane += 1;
        }
        bytes
    }
    fn opening_batch(coefficients: &[Message<E>], gamma: E) -> Vec<E> {
        let gp = crate::prover_powers::powers::<29>(gamma);
        let mut q = Vec::with_capacity(1024);
        let mut row = 0;
        while row < 1024 {
            let value = opening_row(coefficients, &gp, row);
            q.push(value);
            row += 1;
        }
        q
    }
    #[inline(always)]
    fn opening_row(coefficients: &[Message<E>], gp: &[E; 29], row: usize)
        -> E {
        let mut value = E::ZERO;
        let mut lane = 0;
        while lane < 29 {
            value = value.add(gp[lane].mul(coefficients[lane][row]));
            lane += 1;
        }
        value
    }
    fn opening_inactive(q: &[E], w: &Weights) -> E {
        let mut inactive = E::ZERO;
        let mut row = 0;
        while row < 1024 {
            inactive = inactive.add(q[row].mul_qm31(w.raw(0, row)));
            row += 1;
        }
        inactive
    }
    /// Owned input to the publication phase. Constructed only after P_R1 accepts.
    struct Publication {
        backend: Backend,
        semantic_bytes: Vec<u8>,
        y1: Vec<u8>,
        inactive: E,
        c0bytes: Vec<u8>,
        root: [u8; 32],
        c1bytes: Vec<u8>,
        fbytes: Vec<u8>,
        queries: [u32; 22],
        folded_word: Vec<E>,
        folded_salts: PrivateSalts,
        tree: crate::host_tree::BinaryTree,
    }
    fn folded_leaves(hash: HashFn, word: &[E], salts: &PrivateSalts)
        -> Vec<[u8; 32]> {
        let mut leaves = Vec::with_capacity(1 << 18);
        let mut u = 0;
        while u < 1 << 18 {
            let mut values = [0u8; 128];
            if u < 1 << 16 {
                let mut s = 0;
                while s < 4 {
                    values[32 *
                                    s..32 *
                                    (s + 1)].copy_from_slice(&word[4 * u + s].to_le_bytes());
                    s += 1;
                }
            }
            let leaf =
                aspis_core::state_only_private_merkle::private_leaf_hash(hash,
                    0x72, &values, salts.get(u));
            leaves.push(leaf);
            u += 1;
        }
        leaves
    }
    fn finish_opening(variant: Variant, hash: HashFn,
        prepared: PreparedOpening, folded_salts: PrivateSalts)
        -> Result<Publication, Error> {
        let PreparedOpening {
                backend,
                sem,
                mut transcript,
                y1,
                gamma,
                inactive,
                kappa,
                alpha0,
                c0bytes,
                q1,
                w1,
                folded_word } = prepared;
        let leaves = folded_leaves(hash, &folded_word, &folded_salts);
        let tree =
            crate::host_tree::BinaryTree::new(LegacyHashFn(hash),
                        leaves).ok_or(Error::Allocation)?;
        let root = tree.root();
        let c1 = round(&q1, &w1);
        let c1bytes = encoded_slice(&c1);
        let mut payload = root.to_vec();
        payload.extend_from_slice(&c1bytes);
        let alpha1 = transcript.scalar(30, &payload, false);
        let final_message = fold(&q1, alpha1, false);
        let fbytes = encoded_slice(&final_message);
        let queries = transcript.queries(31, &fbytes)?;
        let _rho = transcript.scalar_k(32, &[]);
        public_check(variant,
                &R1PublicChallenges {
                        alpha: sem.alpha,
                        z: [[sem.z[0].x, sem.z[0].y], [sem.z[1].x, sem.z[1].y]],
                        gamma,
                        kappa,
                        alpha0,
                        alpha1,
                        queries: queries.to_vec(),
                    }, sem.roots[0])?;
        Ok(Publication {
                backend,
                semantic_bytes: sem.bytes,
                y1,
                inactive,
                c0bytes,
                root,
                c1bytes,
                fbytes,
                queries,
                folded_word,
                folded_salts,
                tree,
            })
    }
    /// Counted insertion and dedup on at most 22 public query indices. Sorting is
    /// explicit so publication does not depend on an opaque standard sort adapter.
    fn publication_indices(queries: &[u32; 22], begin: usize, end: usize,
        folded: bool) -> Vec<u32> {
        let mut out = Vec::with_capacity(end - begin);
        let mut i = begin;
        while i < end {
            let value = if folded { queries[i] / 4 } else { queries[i] };
            let mut at = 0;
            while at < out.len() && out[at] < value { at += 1; }
            if at == out.len() || out[at] != value { out.insert(at, value); }
            i += 1;
        }
        out
    }
    fn publish_compact(variant: Variant, p: Publication)
        -> Result<Vec<u8>, Error> {
        use crate::host_compact as compact;
        let Publication {
                mut backend,
                semantic_bytes,
                y1,
                inactive,
                c0bytes,
                root,
                c1bytes,
                fbytes,
                queries,
                folded_word,
                folded_salts,
                tree } = p;
        let mut out = Vec::with_capacity(compact::PROOF_BYTES);
        out.extend_from_slice(compact::MAGIC);
        out.extend_from_slice(&[variant.tag(), 0, 0, 0, 0, 0, 0, 0]);
        compact::compact_semantic(&semantic_bytes,
                    &mut out).map_err(|_| Error::Semantic)?;
        compact::compact_values(&y1, &mut out).map_err(|_| Error::Semantic)?;
        out.extend_from_slice(&inactive.to_le_bytes());
        out.extend_from_slice(&c0bytes);
        out.extend_from_slice(&root);
        out.extend_from_slice(&c1bytes);
        out.extend_from_slice(&fbytes);
        match (&out.len(), &compact::OFF_OPENINGS) {
            (left_val, right_val) => {
                if !(*left_val == *right_val) {
                    let kind = ::core::panicking::AssertKind::Eq;
                    ::core::panicking::assert_failed(kind, &*left_val,
                        &*right_val, ::core::option::Option::None);
                }
            }
        };
        let cc1 = backend.c1.take().unwrap();
        let cc2 = backend.c2.take().unwrap();
        out =
            append_query_openings(out, &cc1, &cc2, &queries, &folded_word,
                &folded_salts);
        match (&out.len(), &compact::OFF_NODES) {
            (left_val, right_val) => {
                if !(*left_val == *right_val) {
                    let kind = ::core::panicking::AssertKind::Eq;
                    ::core::panicking::assert_failed(kind, &*left_val,
                        &*right_val, ::core::option::Option::None);
                }
            }
        };
        out = append_node_slots(out, &cc1, &cc2, &tree, &queries)?;
        match (&out.len(), &compact::PROOF_BYTES) {
            (left_val, right_val) => {
                if !(*left_val == *right_val) {
                    let kind = ::core::panicking::AssertKind::Eq;
                    ::core::panicking::assert_failed(kind, &*left_val,
                        &*right_val, ::core::option::Option::None);
                }
            }
        };
        Ok(out)
    }
    fn append_node_slots(out: Vec<u8>, cc1: &Commitment, cc2: &Commitment,
        tree: &crate::host_tree::BinaryTree, queries: &[u32; 22])
        -> Result<Vec<u8>, Error> {
        let out = append_node_slot(out, cc1, cc2, tree, queries, 0, 0)?;
        let out = append_node_slot(out, cc1, cc2, tree, queries, 0, 1)?;
        let out = append_node_slot(out, cc1, cc2, tree, queries, 0, 2)?;
        let out = append_node_slot(out, cc1, cc2, tree, queries, 1, 0)?;
        let out = append_node_slot(out, cc1, cc2, tree, queries, 1, 1)?;
        append_node_slot(out, cc1, cc2, tree, queries, 1, 2)
    }
    fn append_node_slot(mut out: Vec<u8>, cc1: &Commitment, cc2: &Commitment,
        tree: &crate::host_tree::BinaryTree, queries: &[u32; 22],
        batch: usize, t: usize) -> Result<Vec<u8>, Error> {
        use crate::compact;
        let begin = if batch == 0 { 0 } else { compact::SPLIT };
        let end = if batch == 0 { compact::SPLIT } else { 22 };
        let idx = publication_indices(queries, begin, end, t == 2);
        let nodes =
            match t {
                        0 => cc1.multiproof(&idx),
                        1 => cc2.multiproof(&idx),
                        _ => tree.multiproof(&idx),
                    }.ok_or(Error::Allocation)?;
        let cap = 32 * compact::SLOT_NODES[3 * batch + t];
        if !(nodes.len() <= cap) {
            ::core::panicking::panic("assertion failed: nodes.len() <= cap")
        };
        out.extend_from_slice(&nodes);
        let padded = out.len() + cap - nodes.len();
        out.resize(padded, 0);
        Ok(out)
    }
    /// The query loop carries only the output buffer and immutable opening data.
    fn append_query_openings(mut out: Vec<u8>, cc1: &Commitment,
        cc2: &Commitment, queries: &[u32; 22], folded_word: &[E],
        folded_salts: &PrivateSalts) -> Vec<u8> {
        let mut i = 0;
        while i < 22 {
            let u = FibreIndex::new(queries[i] as usize).unwrap();
            let mut opening =
                FibreOpening {
                    values: [[E::ZERO; 29]; 4],
                    paths: [[[[0; 32]; 7]; 6]; 2],
                };
            cc1.fill_opening(u, &mut opening);
            cc2.fill_opening(u, &mut opening);
            out = append_opening_values(out, opening);
            out.extend_from_slice(cc1.opening_salt(u).unwrap());
            out.extend_from_slice(cc2.opening_salt(u).unwrap());
            let at = 4 * (u.get() / 4);
            let values = encoded_slice(&folded_word[at..at + 4]);
            out.extend_from_slice(&values);
            out.extend_from_slice(folded_salts.get(u.get() / 4));
            i += 1;
        }
        out
    }
    /// No commitment or publication loan enters this nested byte-assembly loop.
    fn append_opening_values(out: Vec<u8>, opening: FibreOpening) -> Vec<u8> {
        let out = append_opening_base_row(out, &opening.values[0]);
        let out = append_opening_base_row(out, &opening.values[1]);
        let out = append_opening_base_row(out, &opening.values[2]);
        let out = append_opening_base_row(out, &opening.values[3]);
        let out = append_opening_secure_row(out, &opening.values[0]);
        let out = append_opening_secure_row(out, &opening.values[1]);
        let out = append_opening_secure_row(out, &opening.values[2]);
        append_opening_secure_row(out, &opening.values[3])
    }
    fn append_opening_base_row(mut out: Vec<u8>, row: &[E; 29]) -> Vec<u8> {
        let mut lane = 0;
        while lane < 26 {
            let bytes = row[lane].to_le_bytes();
            out.extend_from_slice(&bytes[..4]);
            lane += 1;
        }
        let bytes = row[28].to_le_bytes();
        out.extend_from_slice(&bytes[..16]);
        out
    }
    fn append_opening_secure_row(mut out: Vec<u8>, row: &[E; 29]) -> Vec<u8> {
        let mut lane = 26;
        while lane < 28 {
            let bytes = row[lane].to_le_bytes();
            out.extend_from_slice(&bytes[..16]);
            lane += 1;
        }
        out
    }
    fn prove_from_semantics(public: Public<'_>, variant: Variant,
        hash: HashFn, backend: Backend, sem: BuiltSemantics<LegacyHashFn>,
        salts: (&ReservedStateOnlyAttemptSecrets, StateOnlyHidingContext))
        -> Result<Vec<u8>, Error> {
        let _ = public;
        let prepared = prepare_opening(variant, hash, backend, sem)?;
        let (reserved, context) = salts;
        let folded_salts =
            derive_private_salts(reserved, context, hash, 0x72)?;
        let publication =
            finish_opening(variant, hash, prepared, folded_salts)?;
        publish_compact(variant, publication)
    }
    /// The attempt cap N of the retry loop (D38.3, accepted N = 8).
    pub const ATTEMPT_CAP: usize = 8;
    pub use aspis_z4b_probe::{R1CheckTimes, R1PublicChallenges};
    /// Durations of the P_R1 checks run on this thread since the last call.
    /// Only durations are kept: never a verdict's reason, a challenge or a root.
    pub fn take_check_times() -> Vec<R1CheckTimes> { { Vec::new() } }
    /// P_R1 on one attempt. R1 is variant S2; P_R1 is not defined for the others.
    fn public_check(variant: Variant, challenges: &R1PublicChallenges,
        c1_root: [u8; 32]) -> Result<(), Error> {
        if variant != Variant::S2 { return Err(Error::Semantic); }
        let _ = c1_root;
        let (accepted, times) = aspis_z4b_probe::p_r1_check(challenges);
        let _ = times;
        if accepted { Ok(()) } else { Err(Error::Rejected) }
    }
    /// One published proof from the retry loop.
    pub struct RetriedProof {
        pub proof: Vec<u8>,
        pub audit: MaskedFixtureAudit,
        pub attempts: usize,
    }
    /// D38.3 retry loop with fresh OS attempt secrets for every attempt.
    pub fn prove_masked_retrying(public: Public<'_>,
        compiled: &PoolV1PairForestMergedC1CompilationV1, variant: Variant,
        hash: HashFn, nonce_store: &mut DurableStateOnlyMaskNonceStore)
        -> Result<RetriedProof, Error> {
        prove_masked_retrying_with(public, compiled, variant, hash,
            nonce_store,
            |_|
                StateOnlyAttemptSecrets::generate().map_err(|_|
                        Error::Entropy))
    }
    /// D38.3 retry loop. `next_attempt(k)` must return fresh OS-generated secrets
    /// for attempt k; a client that binds the nonce to the proof-account address
    /// (D38.4) generates a fresh account keypair per attempt and calls
    /// `StateOnlyAttemptSecrets::generate_for_mask_nonce` with its public key.
    ///
    /// Each attempt durably burns its nonce in `nonce_store` before any mask or
    /// salt is derived (`reserve_and_build_…`). As in Lean `realGameP`
    /// (R1Z/GamesR1P.lean:184: accept on `P ∧ VR1 ∧ ¬ exh`), an attempt is
    /// rejected when its challenges fail P_R1, when χ is a LogUp pole (`¬ VR1`,
    /// LOG D40.3, D73.4.1), or when its mask decode is exhausted (`exh`,
    /// D73.4.2). Each returns the same detail-free `Error::Rejected` before any
    /// proof byte exists; its secrets are dropped (zeroized), it consumes one of
    /// the `ATTEMPT_CAP` attempts, and nothing about it is returned or logged.
    /// After `ATTEMPT_CAP` rejections the result is `AttemptsExhausted` and
    /// nothing is published (Lean's fixed `failView`, R1Z/GamesR1P.lean:185).
    /// Any other error aborts.
    pub fn prove_masked_retrying_with(public: Public<'_>,
        compiled: &PoolV1PairForestMergedC1CompilationV1, variant: Variant,
        hash: HashFn, nonce_store: &mut DurableStateOnlyMaskNonceStore,
        next_attempt:
            impl FnMut(usize) -> Result<StateOnlyAttemptSecrets, Error>)
        -> Result<RetriedProof, Error> {
        if variant != Variant::S2 { return Err(Error::Semantic); }
        retry_attempt(public, compiled, variant, hash, nonce_store,
            next_attempt, 0)
    }
    fn retry_attempt(public: Public<'_>,
        compiled: &PoolV1PairForestMergedC1CompilationV1, variant: Variant,
        hash: HashFn, nonce_store: &mut DurableStateOnlyMaskNonceStore,
        mut next_attempt:
            impl FnMut(usize) -> Result<StateOnlyAttemptSecrets, Error>,
        k: usize) -> Result<RetriedProof, Error> {
        if k >= ATTEMPT_CAP { return Err(Error::AttemptsExhausted); }
        let attempt = next_attempt(k)?;
        match prove_masked_attempt(public, compiled, variant, hash, attempt,
                nonce_store) {
            Ok((proof, audit)) =>
                Ok(RetriedProof { proof, audit, attempts: k + 1 }),
            Err(Error::Rejected) =>
                retry_attempt(public, compiled, variant, hash, nonce_store,
                    next_attempt, k + 1),
            Err(e) => Err(e),
        }
    }
    fn derive_private_salt_step(reserved: &ReservedStateOnlyAttemptSecrets,
        context: StateOnlyHidingContext, hash: HashFn, tag: u8, index: u32,
        mut salts: Vec<[u8; 32]>) -> Result<Vec<[u8; 32]>, Error> {
        let salt =
            reserved.derive_pool_v1_leaf_salt(hash, context, tag,
                        index).map_err(|_| Error::Semantic)?;
        salts.push(salt);
        Ok(salts)
    }
}
/// Host client for the selected public proof-account nonce route (D162).
#[allow(non_snake_case)]
pub mod RealR1_client {
    //! Host-side proof-account caller selected in LOG D162.
    use aspis_core::HashFn;
    use aspis_prover::state_only_entropy::{
        DurableStateOnlyMaskNonceStore, StateOnlyAttemptSecrets,
    };
    use aspis_statement::pool_v1::{
        pair_forest_semantic_terminal::r0::Public,
        pair_forest_trace::PoolV1PairForestMergedC1CompilationV1,
    };
    use crate::{
        prover::{self, RetriedProof},
        transport::Variant, verifier::Error,
    };
    /// Request the public key of a retained proof account for each entered attempt.
    /// The client keeps the keys, including rejected attempts, and uses the key at
    /// `result.attempts - 1` for the published proof account. This function handles
    /// public keys only; it never creates, funds, deletes or uploads an account.
    ///
    /// Keys may be chosen after prior attempts. The supplied durable ledger is
    /// shared across calls; duplicate keys fail closed, even after rejection.
    /// Only the two private 32-byte seeds come from the OS (E1); reservation uses
    /// the existing atomic, persistent ledger (E2). Errors and the eight-attempt
    /// cap are exactly those of `prove_masked_retrying_with`.
    pub fn prove_for_proof_accounts(public: Public<'_>,
        compiled: &PoolV1PairForestMergedC1CompilationV1, hash: HashFn,
        nonce_store: &mut DurableStateOnlyMaskNonceStore,
        mut proof_account: impl FnMut(usize) -> [u8; 32])
        -> Result<RetriedProof, Error> {
        prover::prove_masked_retrying_with(public, compiled, Variant::S2,
            hash, nonce_store,
            |k|
                {
                    StateOnlyAttemptSecrets::generate_for_mask_nonce(proof_account(k)).map_err(|_|
                            Error::Entropy)
                })
    }
}
pub mod dense {
    //! UNPROVED COST PROBE. Dense native self-consistency evaluator.
    //! Uses E arithmetic, literal 1024-entry rows and original circle folding.
    //! Adopted format (PREREG-PROOF-SIZE-2): reads the compact binary-multiproof
    //! proof with its own expansion, canonical scan and BTreeMap multiproof
    //! reconstruction (independent of `verifier::candidate`); layout constants
    //! come from `crate::compact`.
    use aspis_core::r0::CodeField;
    use alloc::{collections::BTreeMap, vec, vec::Vec};
    use aspis_core::{
        HashFn, field::{WideExact as E, QM31 as K, M31},
        r0::{
            self, domain::{FibreIndex, Point},
            merkle,
        },
        r0_transcript as sample,
    };
    use aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public;
    use crate::{
        compact as c, r1_wire as wire, trace, transport::Variant,
        verifier::Error,
    };
    fn powers(x: E, n: usize) -> Vec<E> {
        let mut a = E::ONE;
        (0..n).map(|_| { let b = a; a = a.mul(x); b }).collect()
    }
    fn value(bytes: &[u8], i: usize) -> E {
        E::from_le_bytes(&bytes[32 * i..32 * i + 32]).unwrap()
    }
    fn eval(poly: &[E], x: E) -> E {
        poly.iter().rev().fold(E::ZERO, |v, &c| v.mul(x).add(c))
    }
    fn dot(a: &[E], b: &[E]) -> E {
        a.iter().zip(b).fold(E::ZERO, |v, (&a, &b)| v.add(a.mul(b)))
    }
    fn semantic_block(hash: HashFn, state: &mut [u8; 32], row: u8,
        record: &[u8]) -> [u8; 32] {
        let absorbed = hash(&[state, &[0, 0xa0 + row], record]);
        let block = hash(&[&absorbed, &[1]]);
        *state = hash(&[&absorbed, &[2]]);
        block
    }
    fn absorb(hash: HashFn, state: &mut [u8; 32], row: u8, b: &[u8]) {
        *state =
            hash(&[state, &[0, 0xa0 + row], &(b.len() as u32).to_le_bytes(),
                            b]);
    }
    fn scalar(hash: HashFn, state: &mut [u8; 32], row: u8, b: &[u8],
        nonzero: bool) -> E {
        absorb(hash, state, row, b);
        let block = hash(&[state, &[1]]);
        *state = hash(&[state, &[2]]);
        let x =
            if nonzero {
                crate::host_sampler::gamma_sample(&block)
            } else { crate::host_sampler::ordinary_sample(&block) };
        trace::value(4, row as usize, x);
        x
    }
    fn queries(hash: HashFn, state: &mut [u8; 32], row: u8, b: &[u8])
        -> Result<[u32; 22], Error> {
        absorb(hash, state, row, b);
        let mut out = [0; 22];
        let mut count = 0;
        let mut draws = 0;
        'blocks:
            for _ in 0..8 {
            let block = hash(&[state, &[1]]);
            *state = hash(&[state, &[2]]);
            for bytes in block.chunks_exact(4) {
                if count == 22 || draws == 64 { break 'blocks; }
                draws += 1;
                let q =
                    u32::from_le_bytes(bytes.try_into().unwrap()) &
                        ((1 << 18) - 1);
                if !out[..count].contains(&q) { out[count] = q; count += 1; }
            }
        }
        if count != 22 { return Err(Error::Transcript); }
        for (i, &u) in out.iter().enumerate() {
            trace::value(5, i, E::from_m31(M31(u)));
        }
        Ok(out)
    }
    fn row(v: Variant, j: usize) -> usize {
        if v == Variant::D {
            return r0::transport::COEFFICIENT_TO_ROW[j] as usize;
        }
        ((j & 3) << 6) + (((j >> 2) & 3) << 8) + (((j >> 4) & 3) << 4) +
                ((j >> 6) & 3) + (((j >> 8) & 3) << 2)
    }
    fn second_fold(alpha: E, u: usize, values: [E; 4]) -> E {
        let mut matrix = [[E::ZERO; 5]; 4];
        for s in 0..4 {
            let x =
                r0::domain::line_node::<E>(FibreIndex::new(u / 4 * 4 +
                                s).unwrap());
            for j in 0..4 { matrix[s][j] = r0::basis::natural(j, x); }
            matrix[s][4] = values[s];
        }
        for j in 0..4 {
            let pivot = (j..4).find(|&i| matrix[i][j] != E::ZERO).unwrap();
            matrix.swap(j, pivot);
            let inverse = matrix[j][j].try_inv().unwrap();
            for k in j..5 { matrix[j][k] = matrix[j][k].mul(inverse); }
            for i in 0..4 {
                if i != j {
                    let factor = matrix[i][j];
                    for k in j..5 {
                        matrix[i][k] = matrix[i][k].sub(factor.mul(matrix[j][k]));
                    }
                }
            }
        }
        eval(&core::array::from_fn::<_, 4, _>(|j| matrix[j][4]), alpha)
    }
    /// The compact proof viewed in its logical (32-byte value) form.
    struct Dense {
        variant: Variant,
        semantic: Vec<u8>,
        y1: Vec<u8>,
        inactive: E,
    }
    fn expand(src: &[u8], dst: &mut Vec<u8>) {
        for v in src.chunks_exact(16) {
            dst.extend_from_slice(v);
            dst.extend_from_slice(&[0; 16]);
        }
    }
    fn wide_ok(b: &[u8]) -> bool {
        b.chunks_exact(32).all(|x| E::from_le_bytes(x).is_some())
    }
    fn parse(proof: &[u8]) -> Result<Dense, Error> {
        if proof.len() != c::PROOF_BYTES || &proof[..8] != c::MAGIC ||
                    proof[8] != Variant::S2.tag() ||
                proof[9..16].iter().any(|&b| b != 0) {
            return Err(Error::Parse);
        }
        let mut semantic = Vec::with_capacity(c::LOGICAL_SEMANTIC);
        let src = &proof[c::OFF_SEMANTIC..c::OFF_Y1];
        semantic.extend_from_slice(&src[..32]);
        let mut at = 32;
        for row in 0..c::SEMANTIC_ROWS {
            let size = wire::row_shape(row).ok_or(Error::Parse)?.1;
            semantic.extend_from_slice(&src[at..at + 5]);
            at += 5;
            if row >= 14 {
                expand(&src[at..at + size / 2], &mut semantic);
                at += size / 2;
            } else {
                semantic.extend_from_slice(&src[at..at + size]);
                at += size;
            }
        }
        if at != src.len() || semantic.len() != c::LOGICAL_SEMANTIC {
            return Err(Error::Parse);
        }
        let mut y1 = Vec::with_capacity(c::LOGICAL_Y1);
        expand(&proof[c::OFF_Y1..c::OFF_INACTIVE], &mut y1);
        if !wide_ok(&y1) ||
                    !wide_ok(&proof[c::OFF_INACTIVE..c::OFF_FOLDED_ROOT]) ||
                !wide_ok(&proof[c::OFF_ROUND1..c::OFF_OPENINGS]) {
            return Err(Error::Parse);
        }
        for i in 0..22 {
            let q = &proof[c::OFF_OPENINGS + i * c::OPENING..][..c::OPENING];
            for s in 0..4 {
                if (0..26).any(|l|
                                    M31::from_le_bytes(q[s * 120 +
                                                                l * 4..s * 120 + l * 4 + 4].try_into().unwrap()).is_none())
                            ||
                            K::from_le_bytes(&q[s * 120 + 104..s * 120 + 120]).is_none()
                        ||
                        (0..2).any(|l|
                                K::from_le_bytes(&q[480 + s * 32 +
                                                        l * 16..480 + s * 32 + l * 16 + 16]).is_none()) {
                    return Err(Error::Parse);
                }
            }
            if !wide_ok(&q[672..800]) { return Err(Error::Parse); }
        }
        let inactive =
            E::from_le_bytes(&proof[c::OFF_INACTIVE..c::OFF_ROUND0]).unwrap();
        Ok(Dense { variant: Variant::S2, semantic, y1, inactive })
    }
    /// Binary multiproof by explicit level maps: occupied nodes keyed by index,
    /// siblings taken from `slot` in ascending order, the slot's unused tail zero.
    fn multiproof(hash: HashFn, root: &[u8; 32],
        leaves: BTreeMap<u32, [u8; 32]>, slot: &[u8]) -> bool {
        let mut level = leaves;
        let mut at = 0usize;
        let take =
            |at: &mut usize| -> Option<[u8; 32]>
                {
                    let x = slot.get(*at..*at + 32)?.try_into().ok()?;
                    *at += 32;
                    Some(x)
                };
        for _ in 0..18 {
            let keys: Vec<u32> = level.keys().copied().collect();
            let mut next = BTreeMap::new();
            let mut i = 0;
            while i < keys.len() {
                let k = keys[i];
                let (l, r) =
                    if k & 1 == 0 {
                        if i + 1 < keys.len() && keys[i + 1] == k + 1 {
                            i += 2;
                            (level[&k], level[&(k + 1)])
                        } else {
                            i += 1;
                            let Some(s) = take(&mut at) else { return false };
                            (level[&k], s)
                        }
                    } else {
                        i += 1;
                        let Some(s) = take(&mut at) else { return false };
                        (s, level[&k])
                    };
                next.insert(k >> 1, hash(&[&[0x12], &l, &r]));
            }
            level = next;
        }
        level.len() == 1 && level.get(&0) == Some(root) &&
            slot[at..].iter().all(|&b| b == 0)
    }
    pub fn verify(public: Public<'_>, proof: &[u8], hash: HashFn)
        -> Result<(), Error> {
        let v = parse(proof)?;
        let prefix =
            wire::Prefix::parse(&v.semantic).map_err(|_| Error::Parse)?;
        let round0 = &proof[c::OFF_ROUND0..c::OFF_FOLDED_ROOT];
        let folded_root: [u8; 32] =
            proof[c::OFF_FOLDED_ROOT..c::OFF_ROUND1].try_into().unwrap();
        let round1 = &proof[c::OFF_ROUND1..c::OFF_FINAL];
        let final_bytes = &proof[c::OFF_FINAL..c::OFF_OPENINGS];
        let pb = public.public_bytes().map_err(|_| Error::Parse)?;
        let mut state =
            hash(&[wire::DOMAIN, &[0], &(pb.len() as u32).to_le_bytes(), &pb,
                            prefix.c1_root]);
        let mut samples = [K::ZERO; 25];
        let mut running = value(prefix.payload(14).unwrap(), 0);
        for row in 0..25u8 {
            let block =
                semantic_block(hash, &mut state, row,
                    prefix.record(row).unwrap());
            samples[row as usize] = sample::qm31_sample(&block);
            trace::value(0, row as usize,
                E::from_qm31(samples[row as usize]));
            if row >= 15 {
                let poly: Vec<E> =
                    (0..28).map(|i|
                                value(prefix.payload(row).unwrap(), i)).collect();
                let boundary = poly.iter().copied().fold(poly[0], E::add);
                let next = eval(&poly, E::from_qm31(samples[row as usize]));
                for (j, x) in
                    [running, boundary, next].into_iter().enumerate() {
                    trace::value(1, 3 * (row as usize - 15) + j, x);
                }
                if boundary != running { return Err(Error::Semantic); }
                running = next;
            }
        }
        let challenges =
            aspis_core::state_only_prefix::r0::Challenges {
                lambda: samples[0],
                chi: samples[1],
                theta: samples[2],
                zc: core::array::from_fn(|j| samples[3 + j]),
                mu: samples[13],
                eta: samples[14],
            };
        let alpha: [K; 10] = core::array::from_fn(|j| samples[15 + j]);
        let claims =
            core::array::from_fn(|p|
                    core::array::from_fn(|l|
                            value(prefix.payload(25).unwrap(), p * 29 + l)));
        let extra: Vec<E> =
            (0..29).map(|l|
                        value(prefix.payload(25).unwrap(), 87 + l)).collect();
        let terminal =
            public.terminal(&claims, &alpha,
                        &challenges).map_err(|_| Error::Semantic)?;
        let masked =
            aspis_core::state_only_hiding::r0::masked_terminal(&claims,
                    &alpha, challenges.eta, terminal).add(extra[28]);
        trace::value(2, 0, terminal);
        trace::value(2, 1, masked);
        if running != masked { return Err(Error::Semantic); }
        let b0 =
            semantic_block(hash, &mut state, 25, prefix.record(25).unwrap());
        let z0 = sample::circle_sample(&b0, sample::CircleRow::First);
        let b1 =
            semantic_block(hash, &mut state, 26, prefix.record(26).unwrap());
        let z1 = sample::circle_sample(&b1, sample::CircleRow::Second);
        if z0 == z1 { return Err(Error::Semantic); }
        let z = [z0, z1];
        for (i, x) in [z0.x, z0.y, z1.x, z1.y].into_iter().enumerate() {
            trace::value(3, i, E::from_qm31(x));
        }
        let transcript_domain: &[u8] = b"UNPROVED:R1:PRIVATE-SALTED:P3";
        state = hash(&[transcript_domain, &[v.variant.tag()], &state]);
        let gamma = scalar(hash, &mut state, 27, &v.y1, true);
        let kappa =
            scalar(hash, &mut state, 28, &v.inactive.to_le_bytes(), false);
        let mut folding =
            ::alloc::boxed::box_assume_init_into_vec_unsafe(::alloc::intrinsics::write_box_via_move(::alloc::boxed::Box::new_uninit(),
                    [scalar(hash, &mut state, 29, round0, false)]));
        {
            let mut b = folded_root.to_vec();
            b.extend_from_slice(round1);
            folding.push(scalar(hash, &mut state, 30, &b, false));
        }
        let query_row = 31;
        let queries = queries(hash, &mut state, query_row, final_bytes)?;
        absorb(hash, &mut state, query_row + 1, &[]);
        let block = hash(&[&state, &[1]]);
        state = hash(&[&state, &[2]]);
        let rho = E::from_qm31(sample::qm31_sample(&block));
        trace::value(4, (query_row + 1) as usize, rho);
        let gp = powers(gamma, 29);
        let kp = powers(kappa, 7);
        let mut claims_batch = [E::ZERO; 7];
        claims_batch[0] = v.inactive;
        for p in 0..3 { claims_batch[p + 1] = dot(&gp, &claims[p]); }
        claims_batch[4] = dot(&gp, &extra);
        let endpoints: Vec<E> =
            (0..29).map(|l| value(prefix.payload(26).unwrap(), l)).collect();
        claims_batch[5] = dot(&gp, &endpoints);
        let endpoints: Vec<E> = (0..29).map(|l| value(&v.y1, l)).collect();
        claims_batch[6] = dot(&gp, &endpoints);
        for (j, &x) in claims_batch.iter().enumerate() {
            trace::value(14, j, x);
        }
        let mut relation = dot(&kp, &claims_batch);
        trace::value(14, 7, relation);
        let final_message: Vec<E> =
            (0..v.variant.final_len()).map(|j|
                        value(final_bytes, j)).collect();
        let mut batch_weights =
            ::alloc::vec::from_elem(E::ZERO, final_message.len());
        let mut rhs = E::ZERO;
        let mut rho_power = E::ONE;
        let roots =
            [*prefix.c1_root, prefix.payload(2).unwrap().try_into().unwrap()];
        let opening =
            |i: usize|
                &proof[c::OFF_OPENINGS + i * c::OPENING..][..c::OPENING];
        for (batch, (lo, hi)) in [(0, 10), (10, 22)].into_iter().enumerate() {
            for tree in 0..3 {
                let mut leaves = BTreeMap::new();
                for i in lo..hi {
                    let q = opening(i);
                    let u = queries[i];
                    let (index, leaf) =
                        match tree {
                            0 =>
                                (u,
                                    hash(&[&[0x10, merkle::C1_TAG], &q[..480], &q[608..640]])),
                            1 =>
                                (u,
                                    hash(&[&[0x10, merkle::C2_TAG], &q[480..608],
                                                    &q[640..672]])),
                            _ =>
                                (u / 4, hash(&[&[0x10, 0x72], &q[672..800], &q[800..832]])),
                        };
                    if let Some(old) = leaves.insert(index, leaf) {
                        if old != leaf { return Err(Error::Merkle); }
                    }
                }
                let slot = 3 * batch + tree;
                let start =
                    c::OFF_NODES +
                        32 * c::SLOT_NODES[..slot].iter().sum::<usize>();
                let root =
                    if tree == 2 { &folded_root } else { &roots[tree] };
                if !multiproof(hash, root, leaves,
                            &proof[start..start + 32 * c::SLOT_NODES[slot]]) {
                    return Err(Error::Merkle);
                }
            }
        }
        for (i, &u) in queries.iter().enumerate() {
            let q = opening(i);
            let mut values = [E::ZERO; 4];
            for s in 0..4 {
                for l in 0..29 {
                    let x =
                        if l < 26 {
                            E::from_m31(M31::from_le_bytes(q[s * 120 +
                                                            l * 4..s * 120 + l * 4 + 4].try_into().unwrap()).unwrap())
                        } else if l == 28 {
                            E::from_qm31(K::from_le_bytes(&q[s * 120 +
                                                        104..s * 120 + 120]).unwrap())
                        } else {
                            E::from_qm31(K::from_le_bytes(&q[480 + s * 32 +
                                                        (l - 26) * 16..480 + s * 32 + (l - 26) * 16 + 16]).unwrap())
                        };
                    values[s] = values[s].add(gp[l].mul(x));
                }
                trace::value(9, 4 * i + s, values[s]);
            }
            let mut folded =
                r0::fold::fold_fibre(folding[0],
                        FibreIndex::new(u as usize).unwrap(), values).unwrap();
            trace::value(10, 2 * i, folded);
            {
                let b = &q[672..800];
                let values = core::array::from_fn(|s| value(b, s));
                if values[u as usize % 4] != folded {
                    return Err(Error::Query);
                }
                folded = second_fold(folding[1], u as usize, values);
                trace::value(10, 2 * i + 1, folded);
            }
            let mut node =
                r0::domain::line_node::<E>(FibreIndex::new(if v.variant.folds()
                                    == 1 {
                                u as usize
                            } else { u as usize / 4 * 4 }).unwrap());
            if v.variant.folds() == 2 {
                for _ in 0..2 {
                    let square = node.mul(node);
                    node = square.add(square).sub(E::ONE);
                }
            }
            for j in 0..final_message.len() {
                let weight = r0::basis::natural(j, node);
                batch_weights[j] =
                    batch_weights[j].add(rho_power.mul(weight));
                trace::value(12, i * final_message.len() + j,
                    batch_weights[j]);
                trace::value(13, i * final_message.len() + j, weight);
            }
            rhs = rhs.add(rho_power.mul(folded));
            trace::value(11, i, rhs);
            rho_power = rho_power.mul(rho);
        }
        for r in 0..folding.len() {
            let b = if r == 0 { round0 } else { round1 };
            let p: Vec<E> = (0..7).map(|j| value(b, j)).collect();
            let left = p[0].add(p[4]);
            let right = relation.mul(E::from_m31(M31(536870912)));
            trace::value(15, 3 * r, left);
            trace::value(15, 3 * r + 1, right);
            if left != right { return Err(Error::Relation); }
            relation = eval(&p, folding[r]);
            trace::value(15, 3 * r + 2, relation);
        }
        let points =
            r0::opening::points_from_alphas(&alpha.map(E::from_qm31));
        let mut paired = [E::ZERO; 7];
        for kind in 0..7 {
            let mut weights: Vec<E> =
                (0..1024).map(|j|
                            match kind {
                                0 =>
                                    if r0::opening::inactive(row(v.variant, j)).unwrap() {
                                        E::ONE
                                    } else { E::ZERO },
                                1..=3 =>
                                    (0..10).fold(E::ONE,
                                        |a, b|
                                            a.mul(if (row(v.variant, j) >> b) & 1 == 0 {
                                                    E::ONE.sub(points[kind - 1][b])
                                                } else { points[kind - 1][b] })),
                                4 =>
                                    if j < 56 {
                                        powers(E::from_qm31(alpha[8 + j / 28]), 28)[j % 28]
                                    } else { E::ZERO },
                                _ => {
                                    let p =
                                        Point {
                                            x: E::from_qm31(z[kind - 5].x),
                                            y: E::from_qm31(z[kind - 5].y),
                                        };
                                    r0::basis::natural(j / 2,
                                            p.x).mul(if j % 2 == 0 { E::ONE } else { p.y })
                                }
                            }).collect();
            for (j, &x) in weights.iter().enumerate() {
                trace::value(6, kind * 1024 + j, x);
            }
            for &alpha in &folding {
                let p = powers(alpha, 4);
                weights =
                    weights.chunks_exact(4).map(|c|
                                c[0].add(p[3].mul(c[1])).add(p[2].mul(c[2])).add(p[1].mul(c[3])).mul(E::from_m31(M31(536870912)))).collect();
            }
            for (j, &x) in weights.iter().enumerate() {
                trace::value(7, kind * final_message.len() + j, x);
            }
            paired[kind] = dot(&final_message, &weights);
            trace::value(8, kind, paired[kind]);
        }
        let pair = dot(&paired, &kp);
        trace::value(16, 0, pair);
        trace::value(16, 1, relation);
        if pair != relation { return Err(Error::Relation); }
        let actual = dot(&final_message, &batch_weights);
        trace::value(17, 0, actual);
        trace::value(17, 1, rhs);
        if actual != rhs { return Err(Error::Query); }
        Ok(())
    }
}
/// G-sim (LOG D44.3): the explicit R1 simulator simE in the ideal game.
pub mod sim {
    //! UNPROVED COST PROBE. G-sim (LOG D44.3): the explicit, witness-free R1
    //! simulator `simE` of R0Z/RefPayload.lean, inside the ideal game of
    //! R1Z/GamesR1.lean (`fsR1.ideal`, design zf1/DESIGN-R1-GAMES.txt §5).
    //!
    //! Input: the public statement only (no compiled trace, no witness) and a
    //! 32-byte seed from which every coin of the ideal game is expanded.
    //! Per attempt k < N = 8 (the ideal game's capped loop on P alone):
    //!   1. coins c_k: the 115 transcript answers, the three roots (C1, C2,
    //!      folded) and the commitment answers (salts, leaf, node digests);
    //!   2. ch := dec(squeeze answers): the prover's own transcript code is run
    //!      with every read answered by the next transcript coin, so the answers
    //!      (hence the decoded challenges) do not depend on the payload bytes;
    //!   3. P_R1(ch) by the same check as the prover (z9e: emit + extracted C3
    //!      checker); rejected → next attempt, exhausted → `AttemptsExhausted`;
    //!   4. the uniform tape t: fresh mask material applied to the ZERO trace
    //!      (lanes 0..15 eligible noise only, mask-only lanes 16..25, H1 padding
    //!      with no helper, G, D): the pure-tape trace τ = tapeLinear(equiv⁻¹ t);
    //!   5. the view Ψ_ch(refPayload + L τ) (see `semantic` below);
    //!   6. VerLog: the transcript reads are re-run on the view's records with
    //!      the same answers and recorded as (address, answer); every opened leaf
    //!      read and every node read on the opened paths is programmed with a
    //!      coin, the top node's answer being the root coin.
    //! Output: the proof bytes and the programmed table. The R1 verifier is then
    //! run against `programmed_hash`, which answers programmed addresses from
    //! the table and every other address with the real hash.
    use crate::host_multilinear::multilinear_evaluate_qm31;
    use alloc::{
        collections::{BTreeMap, BTreeSet},
        vec, vec::Vec,
    };
    use core::cell::RefCell;
    use aspis_core::{
        Digest32, HashFn, circle::SecureCirclePoint, digest::LegacyHashFn,
        field::{WideExact as E, M31, QM31 as K, CM31},
        r0::{
            CodeField, Message, domain::{self, FibreIndex, Point},
            encoder::eval_message, fold::phi_inverse, merkle,
        },
        state_only_hiding::{
            StateOnlyHidingContext, state_only_selected_mask_value,
        },
        state_only_private_merkle::private_leaf_hash_with_digest,
        state_only_sumcheck::{
            evaluate_state_only_polynomial, state_only_boundary_sum,
        },
    };
    use aspis_statement::{
        StateOnlyTraceFoundation,
        pool_v1::pair_forest_semantic_terminal::r0::Public,
    };
    use aspis_prover::{
        HOST_HASH, state_only_entropy::StateOnlyAttemptSecrets,
        state_only_hiding::{
            apply_pool_v1_pair_forest_mask_material_v1,
            apply_pool_v1_pair_forest_h1_padding_mask_v1,
            InMemoryStateOnlyMaskNonceStore,
        },
    };
    use crate::{
        compact, multiproof, transport::Variant, verifier::Error,
        host_weights::Weights, transcript::Transcript,
        r1_wire::{self as wire, Challenges, SemanticTranscript},
        host_semantic::{extra, point_claims},
        prover::{encoded, fold, round, ATTEMPT_CAP, R1PublicChallenges},
    };
    /// Ablations used only to show that the verifier test has teeth: dropping
    /// S₀ from the mask-sum cell, or dropping the round-9 terminal shift.
    #[doc(hidden)]
    pub enum Ablation { None, NoS0, NoShift, }
    #[automatically_derived]
    #[doc(hidden)]
    unsafe impl ::core::clone::TrivialClone for Ablation { }
    #[automatically_derived]
    impl ::core::clone::Clone for Ablation {
        #[inline]
        fn clone(&self) -> Ablation { *self }
    }
    #[automatically_derived]
    impl ::core::marker::Copy for Ablation { }
    #[automatically_derived]
    impl ::core::fmt::Debug for Ablation {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            ::core::fmt::Formatter::write_str(f,
                match self {
                    Ablation::None => "None",
                    Ablation::NoS0 => "NoS0",
                    Ablation::NoShift => "NoShift",
                })
        }
    }
    #[automatically_derived]
    impl ::core::marker::StructuralPartialEq for Ablation { }
    #[automatically_derived]
    impl ::core::cmp::PartialEq for Ablation {
        #[inline]
        fn eq(&self, other: &Ablation) -> bool {
            let __self_discr = ::core::intrinsics::discriminant_value(self);
            let __arg1_discr = ::core::intrinsics::discriminant_value(other);
            __self_discr == __arg1_discr
        }
    }
    #[automatically_derived]
    impl ::core::cmp::Eq for Ablation {
        #[inline]
        #[doc(hidden)]
        #[coverage(off)]
        fn assert_fields_are_eq(&self) {}
    }
    pub type Table = BTreeMap<Vec<u8>, [u8; 32]>;
    pub struct SimTimes {
        /// Steps 1–2 (all attempts).
        pub draw: f64,
        /// Step 3, the P_R1 check (all attempts).
        pub p_r1: f64,
        /// Step 4.
        pub tape: f64,
        /// Step 5, semantic part: mask sum, S₀, ten rounds, claims, OOD.
        pub semantic: f64,
        /// Step 5, opening part: y1, inactive, batched rounds, folds, openings.
        pub opening: f64,
        /// Step 6: Merkle programming, serialisation, transcript recording.
        pub program: f64,
        pub total: f64,
    }
    #[automatically_derived]
    #[doc(hidden)]
    unsafe impl ::core::clone::TrivialClone for SimTimes { }
    #[automatically_derived]
    impl ::core::clone::Clone for SimTimes {
        #[inline]
        fn clone(&self) -> SimTimes {
            let _: ::core::clone::AssertParamIsClone<f64>;
            *self
        }
    }
    #[automatically_derived]
    impl ::core::marker::Copy for SimTimes { }
    #[automatically_derived]
    impl ::core::fmt::Debug for SimTimes {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            let names: &'static _ =
                &["draw", "p_r1", "tape", "semantic", "opening", "program",
                            "total"];
            let values: &[&dyn ::core::fmt::Debug] =
                &[&self.draw, &self.p_r1, &self.tape, &self.semantic,
                            &self.opening, &self.program, &&self.total];
            ::core::fmt::Formatter::debug_struct_fields_finish(f, "SimTimes",
                names, values)
        }
    }
    #[automatically_derived]
    impl ::core::default::Default for SimTimes {
        #[inline]
        fn default() -> SimTimes {
            SimTimes {
                draw: ::core::default::Default::default(),
                p_r1: ::core::default::Default::default(),
                tape: ::core::default::Default::default(),
                semantic: ::core::default::Default::default(),
                opening: ::core::default::Default::default(),
                program: ::core::default::Default::default(),
                total: ::core::default::Default::default(),
            }
        }
    }
    pub struct Simulated {
        pub proof: Vec<u8>,
        pub table: Table,
        pub attempts: usize,
        pub transcript_reads: usize,
        pub commitment_reads: usize,
        pub times: SimTimes,
    }
    /// Coin expander: coin i of attempt k is H(domain ‖ seed ‖ k ‖ stream ‖ i).
    struct Coins {
        seed: [u8; 32],
        attempt: u32,
        stream: u8,
        next: u64,
    }
    impl Coins {
        fn new(seed: [u8; 32], attempt: u32, stream: u8) -> Self {
            Self { seed, attempt, stream, next: 0 }
        }
        fn coin(&mut self) -> [u8; 32] {
            let c =
                HOST_HASH(&[b"UNPROVED:R1:SIM:COIN", &self.seed,
                                &self.attempt.to_le_bytes(), &[self.stream],
                                &self.next.to_le_bytes()]);
            self.next += 1;
            c
        }
        fn nonzero(&mut self) -> [u8; 32] {
            loop { let c = self.coin(); if c != [0; 32] { return c; } }
        }
    }
    fn concat(parts: &[&[u8]]) -> Vec<u8> {
        let mut a = Vec::with_capacity(parts.iter().map(|p| p.len()).sum());
        for p in parts { a.extend_from_slice(p); }
        a
    }
    /// Answers every read with the next pre-drawn transcript coin; optionally
    /// records (address, answer).
    struct CoinState {
        coins: Vec<[u8; 32]>,
        next: usize,
        record: Option<Table>,
        collision: bool,
    }
    struct CoinOracle<'a>(&'a RefCell<CoinState>);
    #[automatically_derived]
    #[doc(hidden)]
    unsafe impl<'a> ::core::clone::TrivialClone for CoinOracle<'a> { }
    #[automatically_derived]
    impl<'a> ::core::clone::Clone for CoinOracle<'a> {
        #[inline]
        fn clone(&self) -> CoinOracle<'a> {
            let _: ::core::clone::AssertParamIsClone<&'a RefCell<CoinState>>;
            *self
        }
    }
    #[automatically_derived]
    impl<'a> ::core::marker::Copy for CoinOracle<'a> { }
    impl Digest32 for CoinOracle<'_> {
        fn digest(&self, parts: &[&[u8]]) -> [u8; 32] {
            let mut s = self.0.borrow_mut();
            let answer = *s.coins.get(s.next).unwrap_or(&[0; 32]);
            s.next += 1;
            if let Some(t) = s.record.as_mut() {
                if let Some(prev) = t.insert(concat(parts), answer) {
                    if prev != answer { s.collision = true; }
                }
            }
            answer
        }
    }
    /// Programs exactly one read: records (address, answer) and returns answer.
    struct ProgramOne<'a> {
        table: &'a RefCell<(Table, bool)>,
        answer: [u8; 32],
    }
    #[automatically_derived]
    #[doc(hidden)]
    unsafe impl<'a> ::core::clone::TrivialClone for ProgramOne<'a> { }
    #[automatically_derived]
    impl<'a> ::core::clone::Clone for ProgramOne<'a> {
        #[inline]
        fn clone(&self) -> ProgramOne<'a> {
            let _:
                    ::core::clone::AssertParamIsClone<&'a RefCell<(Table,
                    bool)>>;
            let _: ::core::clone::AssertParamIsClone<[u8; 32]>;
            *self
        }
    }
    #[automatically_derived]
    impl<'a> ::core::marker::Copy for ProgramOne<'a> { }
    impl Digest32 for ProgramOne<'_> {
        fn digest(&self, parts: &[&[u8]]) -> [u8; 32] {
            let mut t = self.table.borrow_mut();
            if let Some(prev) = t.0.insert(concat(parts), self.answer) {
                if prev != self.answer { t.1 = true; }
            }
            self.answer
        }
    }
    const PROGRAMMED:
        ::std::thread::LocalKey<RefCell<Option<(Table, BTreeSet<Vec<u8>>)>>> =
        {
            const __RUST_STD_INTERNAL_INIT:
                RefCell<Option<(Table, BTreeSet<Vec<u8>>)>> =
                { RefCell::new(None) };
            unsafe {
                ::std::thread::LocalKey::new(const {
                            if ::std::mem::needs_drop::<RefCell<Option<(Table,
                                        BTreeSet<Vec<u8>>)>>>() {
                                |_|
                                    {
                                        #[thread_local]
                                        static __RUST_STD_INTERNAL_VAL:
                                            ::std::thread::local_impl::EagerStorage<RefCell<Option<(Table,
                                            BTreeSet<Vec<u8>>)>>> =
                                            ::std::thread::local_impl::EagerStorage::new(__RUST_STD_INTERNAL_INIT);
                                        __RUST_STD_INTERNAL_VAL.get()
                                    }
                            } else {
                                |_|
                                    {
                                        #[thread_local]
                                        static __RUST_STD_INTERNAL_VAL:
                                            RefCell<Option<(Table, BTreeSet<Vec<u8>>)>> =
                                            __RUST_STD_INTERNAL_INIT;
                                        &__RUST_STD_INTERNAL_VAL
                                    }
                            }
                        })
            }
        };
    /// Install a programmed table for `programmed_hash` on this thread.
    pub fn install(table: Table) {
        PROGRAMMED.with(|p| *p.borrow_mut() = Some((table, BTreeSet::new())));
    }
    /// Remove the table; returns (programmed addresses, addresses actually read).
    pub fn uninstall() -> (usize, usize) {
        PROGRAMMED.with(|p|
                p.borrow_mut().take().map(|(t, hits)|
                            (t.len(), hits.len())).unwrap_or((0, 0)))
    }
    /// The random oracle of the ideal game as the verifier sees it: programmed
    /// answers at published addresses, the real hash everywhere else.
    pub fn programmed_hash(parts: &[&[u8]]) -> [u8; 32] {
        let address = concat(parts);
        let hit =
            PROGRAMMED.with(|p|
                    {
                        let mut p = p.borrow_mut();
                        let (table, hits) = p.as_mut()?;
                        let a = *table.get(&address)?;
                        hits.insert(address.clone());
                        Some(a)
                    });
        hit.unwrap_or_else(|| HOST_HASH(parts))
    }
    struct Records {
        c1_root: [u8; 32],
        semantic: Vec<Vec<u8>>,
        y1: Vec<u8>,
        inactive: [u8; 32],
        c0: Vec<u8>,
        folded_root: [u8; 32],
        c1: Vec<u8>,
        fin: Vec<u8>,
    }
    impl Records {
        fn placeholder() -> Result<Self, Error> {
            let semantic =
                (0..27u8).map(|row|
                                wire::record(row,
                                        &::alloc::vec::from_elem(0,
                                                wire::row_shape(row).unwrap().1)).map_err(|_|
                                        Error::Semantic)).collect::<Result<Vec<_>, _>>()?;
            Ok(Self {
                    c1_root: [0; 32],
                    semantic,
                    y1: ::alloc::vec::from_elem(0, 29 * 32),
                    inactive: [0; 32],
                    c0: ::alloc::vec::from_elem(0, 7 * 32),
                    folded_root: [0; 32],
                    c1: ::alloc::vec::from_elem(0, 7 * 32),
                    fin: ::alloc::vec::from_elem(0, 64 * 32),
                })
        }
    }
    struct Drawn {
        sem: [K; 25],
        z: [SecureCirclePoint; 2],
        gamma: E,
        kappa: E,
        alpha0: E,
        alpha1: E,
        queries: [u32; 22],
        rho: K,
    }
    #[automatically_derived]
    impl ::core::clone::Clone for Drawn {
        #[inline]
        fn clone(&self) -> Drawn {
            Drawn {
                sem: ::core::clone::Clone::clone(&self.sem),
                z: ::core::clone::Clone::clone(&self.z),
                gamma: ::core::clone::Clone::clone(&self.gamma),
                kappa: ::core::clone::Clone::clone(&self.kappa),
                alpha0: ::core::clone::Clone::clone(&self.alpha0),
                alpha1: ::core::clone::Clone::clone(&self.alpha1),
                queries: ::core::clone::Clone::clone(&self.queries),
                rho: ::core::clone::Clone::clone(&self.rho),
            }
        }
    }
    #[automatically_derived]
    impl ::core::marker::StructuralPartialEq for Drawn { }
    #[automatically_derived]
    impl ::core::cmp::PartialEq for Drawn {
        #[inline]
        fn eq(&self, other: &Drawn) -> bool {
            self.sem == other.sem && self.z == other.z &&
                                    self.gamma == other.gamma && self.kappa == other.kappa &&
                            self.alpha0 == other.alpha0 && self.alpha1 == other.alpha1
                    && self.queries == other.queries && self.rho == other.rho
        }
    }
    /// The prover's transcript order (host_semantic rows 0..26, then the opening
    /// rows 27..32 of prove_from_semantics): 115 reads.
    fn walk<H: Digest32>(hash: H, public_bytes: &[u8], r: &Records,
        variant: Variant) -> Result<Drawn, Error> {
        let mut st =
            SemanticTranscript::new(hash, public_bytes,
                        &r.c1_root).map_err(|_| Error::Semantic)?;
        let mut sem = [K::ZERO; 25];
        for row in 0..25u8 {
            sem[row as usize] =
                st.semantic(row,
                            &r.semantic[row as usize]).map_err(|_| Error::Semantic)?;
        }
        let z0 =
            st.challenge_reference_circle_point(25,
                        &r.semantic[25]).map_err(|_| Error::Semantic)?;
        let z1 =
            st.challenge_reference_circle_point(26,
                        &r.semantic[26]).map_err(|_| Error::Semantic)?;
        let mut t = Transcript::new(hash, st.state(), variant);
        let gamma = t.scalar(27, &r.y1, true);
        let kappa = t.scalar(28, &r.inactive, false);
        let alpha0 = t.scalar(29, &r.c0, false);
        let mut payload = r.folded_root.to_vec();
        payload.extend_from_slice(&r.c1);
        let alpha1 = t.scalar(30, &payload, false);
        let queries = t.queries(31, &r.fin)?;
        let rho = t.scalar_k(32, &[]);
        Ok(Drawn {
                sem,
                z: [z0, z1],
                gamma,
                kappa,
                alpha0,
                alpha1,
                queries,
                rho,
            })
    }
    struct Tape {
        c1: [Vec<M31>; 26],
        h1: Vec<K>,
        g: Vec<K>,
        d: Vec<K>,
    }
    /// The pure-tape trace: the prover's mask material (same derivation, fresh
    /// entropy from the coins) applied to the zero C1 trace; H1 is the padding
    /// alone (no copy helper is built).
    fn tape(public_bytes: &[u8], variant: Variant, coins: &mut Coins)
        -> Result<Tape, Error> {
        let hash = HOST_HASH;
        let nonce = coins.nonzero();
        let context =
            StateOnlyHidingContext::pool_v1_pair_forest_v1(hash(&[public_bytes]),
                nonce);
        let binding =
            hash(&[b"UNPROVED:R1:P3:PRIVATE-ATTEMPT", public_bytes,
                            &[variant.tag()], &context.encode()]);
        let secrets =
            StateOnlyAttemptSecrets::deterministic_spend_fixture(nonce,
                coins.nonzero(), coins.nonzero());
        let mut store = InMemoryStateOnlyMaskNonceStore::default();
        let (reserved, material) =
            secrets.reserve_and_build_pool_v1_pair_forest_mask_material_v1(hash,
                        binding, context, &mut store).map_err(|_| Error::Semantic)?;
        let mut zero =
            StateOnlyTraceFoundation {
                c1: core::array::from_fn(|_|
                        ::alloc::vec::from_elem(M31::ZERO, 1024)),
            };
        let applied =
            apply_pool_v1_pair_forest_mask_material_v1(&mut zero,
                        material).map_err(|_| Error::Semantic)?;
        let d =
            reserved.derive_pool_v1_pair_forest_zero_factor_d(hash,
                        context).map_err(|_| Error::Semantic)?;
        let mut h1 = ::alloc::vec::from_elem(K::ZERO, 1024);
        apply_pool_v1_pair_forest_h1_padding_mask_v1(&mut h1,
                    &applied.h1_padding).map_err(|_| Error::Semantic)?;
        if zero.c1.len() != 16 || d.len() != 1024 || applied.g.len() != 1024
                ||
                crate::prover_helper_sum::state_only_copy_helper_sum(&h1) !=
                    Some(K::ZERO) {
            return Err(Error::Semantic);
        }
        let c1 =
            core::array::from_fn(|i|
                    if i < 16 {
                        zero.c1[i].clone()
                    } else { applied.mask_only_c1[i - 16].clone() });
        Ok(Tape { c1, h1, g: applied.g.clone(), d })
    }
    fn tcheb(x: M31) -> M31 { x.mul(x).double().sub(M31::ONE) }
    /// EncodingDomain levels[d][j >> d] for d = 0..8: the only nodes that the
    /// evaluation of index j at depth 0 reads (levels[d][i] = T^(d+1)(x_(i·2^d))).
    fn nodes_for(j: usize) -> [M31; 9] {
        core::array::from_fn(|depth|
                {
                    let p =
                        domain::fibre_point::<M31>(FibreIndex::new((j >> depth) <<
                                        depth).unwrap());
                    let mut n = tcheb(p.x);
                    for _ in 0..depth { n = tcheb(n); }
                    n
                })
    }
    fn eval_rec<T: CodeField>(coefficients: &[T], depth: usize,
        nodes: &[M31; 9]) -> T {
        if coefficients.len() == 1 { return coefficients[0]; }
        let even: Vec<T> = coefficients.iter().step_by(2).copied().collect();
        let odd: Vec<T> =
            coefficients.iter().skip(1).step_by(2).copied().collect();
        eval_rec(&even, depth + 1,
                nodes).add(T::from_m31(nodes[depth]).mul(eval_rec(&odd,
                    depth + 1, nodes)))
    }
    /// EncodingDomain::evaluate(coefficients, 0)[j] at one index (≤ 256 coefficients).
    pub(crate) fn eval_at<T: CodeField>(coefficients: &[T], j: usize) -> T {
        eval_rec(coefficients, 0, &nodes_for(j))
    }
    /// EncodingDomain::encode(coefficients)[4u..4u+4] at one fibre.
    pub(crate) fn encode_at<T: CodeField>(coefficients: &[T; 1024], u: usize)
        -> [T; 4] {
        let z = domain::fibre_point::<M31>(FibreIndex::new(u).unwrap());
        let nodes = nodes_for(u);
        let channels =
            core::array::from_fn(|s|
                    {
                        let c: Vec<T> =
                            (0..256).map(|d| coefficients[4 * d + s]).collect();
                        eval_rec(&c, 0, &nodes)
                    });
        phi_inverse(T::from_m31(z.x), T::from_m31(z.y), channels)
    }
    struct View5 {
        semantic: Vec<Vec<u8>>,
        y1: Vec<u8>,
        inactive: [u8; 32],
        c0: Vec<u8>,
        c1: Vec<u8>,
        fin: Vec<u8>,
        q1: Vec<E>,
        messages: Vec<Message<E>>,
    }
    fn challenges_of(d: &Drawn) -> Challenges {
        Challenges {
            lambda: d.sem[0],
            chi: d.sem[1],
            theta: d.sem[2],
            zc: core::array::from_fn(|i| d.sem[3 + i]),
            mu: d.sem[13],
            eta: d.sem[14],
        }
    }
    /// Step 5, semantic part: Ψ_ch(refPayload + L τ) on the semantic cells.
    ///   mask-sum cell   Σ_b maskLinear(τ)(b) + S₀,  S₀ = Σ_b η·terminal(0)(b)
    ///   round cells     rounds(maskLinear(τ) + η·terminal(0))  [L τ + originalRounds(0)]
    ///                   + (originalOf − η·terminal(0)(α))·(α₉−½)⁻¹·(X−½) on round 9
    ///                   [−k₀·dir from refPayload, then Ψ_ch]
    ///   claims, extra, OOD cells   those of τ  [L τ; refPayload is 0 there]
    fn semantic(public: Public<'_>, tau: &Tape, d: &Drawn, c2_root: &[u8; 32],
        variant: Variant, ablation: Ablation)
        -> Result<(Vec<Vec<u8>>, [Vec<K>; 29]), Error> {
        let ch = challenges_of(d);
        let alpha: [K; 10] = core::array::from_fn(|i| d.sem[15 + i]);
        let lift = |x: M31| K::from_cm31(CM31::from_m31(x));
        let columns: [Vec<K>; 29] =
            core::array::from_fn(|lane|
                    match lane {
                        0..=25 => tau.c1[lane].iter().copied().map(lift).collect(),
                        26 => tau.h1.clone(),
                        27 => tau.g.clone(),
                        _ => tau.d.clone(),
                    });
        let d28: &[K; 1024] = columns[28].as_slice().try_into().unwrap();
        let dc = variant.coefficients(d28);
        let zero = [[K::ZERO; 29]; 3];
        let term0 =
            |p: &[K; 10]|
                crate::host_public::terminal_qm31(public, &zero, p,
                        &ch).map_err(|_| Error::Semantic);
        let bits =
            |row: usize| -> [K; 10]
                {
                    core::array::from_fn(|i|
                            if (row >> (9 - i)) & 1 == 0 { K::ZERO } else { K::ONE })
                };
        let mut mask_sum = K::ZERO;
        let mut s0 = K::ZERO;
        for row in 0..1024 {
            let point = bits(row);
            mask_sum =
                mask_sum.add(state_only_selected_mask_value(&core::array::from_fn(|i|
                                    columns[i][row]),
                        &core::array::from_fn(|i| columns[16 + i][row]),
                        columns[27][row], &point));
            s0 = s0.add(ch.eta.mul(term0(&point)?));
        }
        for side in 0..2 {
            let h = &dc[28 * side..28 * (side + 1)];
            mask_sum =
                mask_sum.add(h.iter().copied().fold(h[0],
                            K::add).mul_m31(M31(512)));
        }
        let mask_cell =
            if ablation == Ablation::NoS0 {
                mask_sum
            } else { mask_sum.add(s0) };
        let f =
            |p: &[K; 10]| -> Result<K, Error>
                {
                    let at = wire::statement_points(p)[0];
                    let ev =
                        |l: usize|
                            multilinear_evaluate_qm31(&columns[l],
                                    &at).ok_or(Error::Semantic);
                    let mut c1 = [K::ZERO; 16];
                    for (i, c) in c1.iter_mut().enumerate() { *c = ev(i)?; }
                    let mut mo = [K::ZERO; 10];
                    for (i, c) in mo.iter_mut().enumerate() {
                        *c = ev(16 + i)?;
                    }
                    let mask =
                        state_only_selected_mask_value(&c1, &mo, ev(27)?, p);
                    Ok(mask.add(extra(&dc, p[8],
                                    p[9])).add(ch.eta.mul(term0(p)?)))
                };
        let mut polys = [[K::ZERO; 28]; 10];
        let mut point = [K::ZERO; 10];
        let mut running = mask_cell;
        for r in 0..10 {
            let remaining = 9 - r;
            let mut values = [K::ZERO; 28];
            for (sample, value) in values.iter_mut().enumerate() {
                point[r] = K::from_cm31(CM31::from_m31(M31(sample as u32)));
                for assignment in 0..1usize << remaining {
                    for offset in 0..remaining {
                        point[r + 1 + offset] =
                            if (assignment >> (remaining - 1 - offset)) & 1 == 0 {
                                K::ZERO
                            } else { K::ONE };
                    }
                    *value = value.add(f(&point)?);
                }
            }
            polys[r] = crate::host_sumcheck::interpolate(&values);
            if ablation != Ablation::NoS0 &&
                    state_only_boundary_sum(&polys[r]) != running {
                return Err(Error::Semantic);
            }
            point[r] = alpha[r];
            running = evaluate_state_only_polynomial(&polys[r], alpha[r]);
        }
        let claims =
            point_claims(&columns, &alpha).map_err(|_| Error::Semantic)?;
        let extras: [K; 29] =
            core::array::from_fn(|l|
                    extra(&variant.coefficients(columns[l].as_slice().try_into().unwrap()),
                        alpha[8], alpha[9]));
        let original =
            ch.eta.mul(crate::host_public::terminal_qm31(public, &claims,
                            &alpha, &ch).map_err(|_| Error::Semantic)?);
        let half = K::from_cm31(CM31::from_m31(M31(2).inv()));
        let inv = alpha[9].sub(half).try_inv().ok_or(Error::Semantic)?;
        if ablation != Ablation::NoShift {
            let c = original.sub(ch.eta.mul(term0(&alpha)?)).mul(inv);
            polys[9][0] = polys[9][0].sub(c.mul(half));
            polys[9][1] = polys[9][1].add(c);
        }
        if ablation == Ablation::None {
            let mask =
                state_only_selected_mask_value(&core::array::from_fn(|i|
                                claims[0][i]), &core::array::from_fn(|i| claims[0][16 + i]),
                    claims[0][27], &alpha);
            if evaluate_state_only_polynomial(&polys[9], alpha[9]) !=
                    mask.add(original).add(extras[28]) {
                return Err(Error::Semantic);
            }
        }
        let rec =
            |row: u8, payload: &[u8]|
                wire::record(row, payload).map_err(|_| Error::Semantic);
        let mut out = Vec::with_capacity(27);
        for row in 0..15u8 {
            out.push(match row {
                    2 => rec(2, c2_root)?,
                    14 => rec(14, &E::from_qm31(mask_cell).to_le_bytes())?,
                    _ => rec(row, &[])?,
                });
        }
        for (r, p) in polys.iter().enumerate() {
            out.push(rec(15 + r as u8,
                        &wire::encode_values(p.map(E::from_qm31)))?);
        }
        out.push(rec(25,
                    &wire::encode_values(claims.into_iter().flatten().chain(extras).map(E::from_qm31)))?);
        let z0 = d.z[0];
        let endpoint =
            columns.iter().map(|col|
                    {
                        let m: &[K; 1024] = col.as_slice().try_into().unwrap();
                        E::from_qm31(eval_message(&variant.coefficients(m),
                                Point { x: z0.x, y: z0.y }))
                    });
        out.push(rec(26, &wire::encode_values(endpoint))?);
        Ok((out, columns))
    }
    /// Step 5, opening part: the linear cells of τ (prove_from_semantics' formulas).
    fn opening(columns: &[Vec<K>; 29], tau: &Tape, d: &Drawn,
        variant: Variant) -> Result<View5, Error> {
        let messages: Vec<Message<E>> =
            (0..29).map(|l|
                        if l < 26 {
                            core::array::from_fn(|r| E::from_m31(tau.c1[l][r]))
                        } else {
                            core::array::from_fn(|r| E::from_qm31(columns[l][r]))
                        }).collect();
        let coefficients: Vec<Message<E>> =
            messages.iter().map(|m| variant.coefficients(m)).collect();
        let z1 =
            Point { x: E::from_qm31(d.z[1].x), y: E::from_qm31(d.z[1].y) };
        let y1 = encoded(coefficients.iter().map(|m| eval_message(m, z1)));
        let gp = crate::prover_powers::powers::<29>(d.gamma);
        let q: Vec<E> =
            (0..1024).map(|j|
                        (0..29).fold(E::ZERO,
                            |s, l| s.add(gp[l].mul(coefficients[l][j])))).collect();
        let alpha: [K; 10] = core::array::from_fn(|i| d.sem[15 + i]);
        let w = Weights::new(variant, &alpha, &d.z)?;
        let inactive =
            (0..1024).fold(E::ZERO, |s, j| s.add(q[j].mul_qm31(w.raw(0, j))));
        let mut weights =
            match aspis_core::r0::heap::filled(1024, E::ZERO) {
                Ok(v) => v,
                Err(_) => return Err(Error::Allocation),
            };
        w.materialize(d.kappa, weights.as_mut_slice().try_into().unwrap())?;
        let c0 = encoded(round(&q, &weights));
        let q1 = fold(&q, d.alpha0, false);
        let w1 = fold(&weights, d.alpha0, true);
        let c1 = encoded(round(&q1, &w1));
        let fin = encoded(fold(&q1, d.alpha1, false).into_iter());
        Ok(View5 {
                semantic: ::alloc::vec::Vec::new(),
                y1,
                inactive: inactive.to_le_bytes(),
                c0,
                c1,
                fin,
                q1,
                messages,
            })
    }
    /// Sparse binary tree containing exactly the opened path union. Sibling
    /// digests are coins, stored for multiproof assembly without oracle reads.
    struct ProgrammedTree {
        children: Vec<BTreeMap<usize, [[u8; 32]; 2]>>,
    }
    impl ProgrammedTree {
        fn multiproof(&self, indices: &[u32]) -> Result<Vec<u8>, Error> {
            multiproof::generate(multiproof::Arity::Two, indices,
                    |depth, index|
                        {
                            self.children[depth as
                                            usize][&(index as usize / 2)][index as usize % 2]
                        }).ok_or(Error::Merkle)
        }
    }
    /// Program leaves and each distinct binary parent in the union of both
    /// transaction batches. Shared nodes receive one consistent answer, including
    /// the root coin. Each batch later emits its own canonical sibling sequence.
    fn program_tree(table: &RefCell<(Table, bool)>, coins: &mut Coins,
        tag: u8, leaves: &BTreeMap<usize, (Vec<u8>, [u8; 32])>,
        root: [u8; 32]) -> Result<(ProgrammedTree, usize), Error> {
        let mut reads = 0;
        let mut level = BTreeMap::new();
        for (&i, (value, salt)) in leaves {
            let answer = coins.coin();
            private_leaf_hash_with_digest(ProgramOne { table, answer }, tag,
                value, salt);
            level.insert(i, answer);
            reads += 1;
        }
        let mut children = Vec::new();
        for depth in 0..multiproof::LEAF_BITS {
            let parents: BTreeSet<usize> =
                level.keys().map(|i| i / 2).collect();
            let (mut next, mut kids_here) =
                (BTreeMap::new(), BTreeMap::new());
            for p in parents {
                let kids =
                    core::array::from_fn(|s|
                            level.get(&(2 * p +
                                                    s)).copied().unwrap_or_else(|| coins.coin()));
                let answer =
                    if depth + 1 == multiproof::LEAF_BITS {
                        root
                    } else { coins.coin() };
                multiproof::binary_parent(ProgramOne { table, answer },
                    &kids[0], &kids[1]);
                reads += 1;
                next.insert(p, answer);
                kids_here.insert(p, kids);
            }
            children.push(kids_here);
            level = next;
        }
        if level.len() != 1 || level.get(&0) != Some(&root) {
            return Err(Error::Merkle);
        }
        Ok((ProgrammedTree { children }, reads))
    }
    pub fn sim_e(public: Public<'_>, seed: [u8; 32])
        -> Result<Simulated, Error> {
        sim_e_ablated(public, seed, Ablation::None)
    }
    #[doc(hidden)]
    pub fn sim_e_ablated(public: Public<'_>, seed: [u8; 32],
        ablation: Ablation) -> Result<Simulated, Error> {
        let variant = Variant::S2;
        let start = std::time::Instant::now();
        let mut times = SimTimes::default();
        let public_bytes =
            crate::host_public::materialize_public_bytes(public).map_err(|_|
                        Error::Semantic)?;
        for k in 0..ATTEMPT_CAP {
            let t = std::time::Instant::now();
            let mut transcript_coins = Coins::new(seed, k as u32, 0);
            let mut root_coins = Coins::new(seed, k as u32, 1);
            let mut commit_coins = Coins::new(seed, k as u32, 2);
            let mut tape_coins = Coins::new(seed, k as u32, 3);
            let answers: Vec<[u8; 32]> =
                (0..115).map(|_| transcript_coins.coin()).collect();
            let roots =
                [root_coins.coin(), root_coins.coin(), root_coins.coin()];
            let state =
                RefCell::new(CoinState {
                        coins: answers,
                        next: 0,
                        record: None,
                        collision: false,
                    });
            let drawn =
                walk(CoinOracle(&state), &public_bytes,
                    &Records::placeholder()?, variant);
            times.draw += t.elapsed().as_secs_f64();
            let drawn =
                match drawn {
                    Ok(d) if state.borrow().next == 115 && d.z[0] != d.z[1] =>
                        d,
                    _ => continue,
                };
            let t = std::time::Instant::now();
            let check =
                R1PublicChallenges {
                    alpha: core::array::from_fn(|i| drawn.sem[15 + i]),
                    z: [[drawn.z[0].x, drawn.z[0].y],
                            [drawn.z[1].x, drawn.z[1].y]],
                    gamma: drawn.gamma,
                    kappa: drawn.kappa,
                    alpha0: drawn.alpha0,
                    alpha1: drawn.alpha1,
                    queries: drawn.queries.to_vec(),
                };
            let (accepted, _) = aspis_z4b_probe::p_r1_check(&check);
            times.p_r1 += t.elapsed().as_secs_f64();
            if !accepted { continue; }
            let t = std::time::Instant::now();
            let tau = tape(&public_bytes, variant, &mut tape_coins)?;
            times.tape = t.elapsed().as_secs_f64();
            let t = std::time::Instant::now();
            let (semantic_records, columns) =
                semantic(public, &tau, &drawn, &roots[1], variant, ablation)?;
            times.semantic = t.elapsed().as_secs_f64();
            let t = std::time::Instant::now();
            let mut view = opening(&columns, &tau, &drawn, variant)?;
            view.semantic = semantic_records;
            times.opening = t.elapsed().as_secs_f64();
            let t = std::time::Instant::now();
            let table = RefCell::new((Table::new(), false));
            let coeffs: Vec<Message<E>> =
                view.messages.iter().map(|m|
                            variant.coefficients(m)).collect();
            let base: Vec<[M31; 1024]> =
                (0..26).map(|l|
                            coeffs[l].map(|x| M31(x.to_limbs()[0]))).collect();
            let ext: Vec<[K; 1024]> =
                (26..29).map(|l| coeffs[l].map(|x| x.c0())).collect();
            let mut opened:
                    BTreeMap<usize, ([[E; 29]; 4], Vec<u8>, Vec<u8>)> =
                BTreeMap::new();
            for &u in &drawn.queries {
                let u = u as usize;
                let mut values = [[E::ZERO; 29]; 4];
                for l in 0..26 {
                    let v = encode_at(&base[l], u);
                    for s in 0..4 { values[s][l] = E::from_m31(v[s]); }
                }
                for l in 26..29 {
                    let v = encode_at(&ext[l - 26], u);
                    for s in 0..4 { values[s][l] = E::from_qm31(v[s]); }
                }
                let mut c1v = Vec::with_capacity(480);
                let mut c2v = Vec::with_capacity(128);
                for s in 0..4 {
                    for l in (0..26).chain(core::iter::once(28)) {
                        c1v.extend_from_slice(&values[s][l].to_le_bytes()[..if l <
                                                26 {
                                            4
                                        } else { 16 }]);
                    }
                }
                for s in 0..4 {
                    for l in 26..28 {
                        c2v.extend_from_slice(&values[s][l].to_le_bytes()[..16]);
                    }
                }
                opened.insert(u, (values, c1v, c2v));
            }
            let mut folded: BTreeMap<usize, Vec<u8>> = BTreeMap::new();
            for &u in &drawn.queries {
                let v = u as usize / 4;
                folded.entry(v).or_insert_with(||
                        encoded((4 * v..4 * v + 4).map(|i| eval_at(&view.q1, i))));
            }
            let mut leaves1 = BTreeMap::new();
            let mut leaves2 = BTreeMap::new();
            let mut leavesf = BTreeMap::new();
            for (&u, (_, c1v, c2v)) in &opened {
                leaves1.insert(u, (c1v.clone(), commit_coins.coin()));
                leaves2.insert(u, (c2v.clone(), commit_coins.coin()));
            }
            for (&v, fv) in &folded {
                leavesf.insert(v, (fv.clone(), commit_coins.coin()));
            }
            let (p1, r1) =
                program_tree(&table, &mut commit_coins, merkle::C1_TAG,
                        &leaves1, roots[0])?;
            let (p2, r2) =
                program_tree(&table, &mut commit_coins, merkle::C2_TAG,
                        &leaves2, roots[1])?;
            let (pf, rf) =
                program_tree(&table, &mut commit_coins, 0x72, &leavesf,
                        roots[2])?;
            let records =
                Records {
                    c1_root: roots[0],
                    semantic: view.semantic.clone(),
                    y1: view.y1.clone(),
                    inactive: view.inactive,
                    c0: view.c0.clone(),
                    folded_root: roots[2],
                    c1: view.c1.clone(),
                    fin: view.fin.clone(),
                };
            let mut out = Vec::with_capacity(compact::PROOF_BYTES);
            out.extend_from_slice(compact::MAGIC);
            out.extend_from_slice(&[variant.tag(), 0, 0, 0, 0, 0, 0, 0]);
            let mut logical = records.c1_root.to_vec();
            for r in &records.semantic { logical.extend_from_slice(r); }
            compact::compact_semantic(&logical,
                        &mut out).map_err(|_| Error::Semantic)?;
            compact::compact_values(&records.y1,
                        &mut out).map_err(|_| Error::Semantic)?;
            out.extend_from_slice(&records.inactive);
            out.extend_from_slice(&records.c0);
            out.extend_from_slice(&records.folded_root);
            out.extend_from_slice(&records.c1);
            out.extend_from_slice(&records.fin);
            for &u in &drawn.queries {
                let u = u as usize;
                let (_, c1v, c2v) = &opened[&u];
                out.extend_from_slice(c1v);
                out.extend_from_slice(c2v);
                out.extend_from_slice(&leaves1[&u].1);
                out.extend_from_slice(&leaves2[&u].1);
                out.extend_from_slice(&folded[&(u / 4)]);
                out.extend_from_slice(&leavesf[&(u / 4)].1);
            }
            if out.len() != compact::OFF_NODES { return Err(Error::Parse); }
            for (batch, range) in
                [(0, 0..compact::SPLIT),
                        (1, compact::SPLIT..compact::QUERIES)] {
                for (tree, programmed) in
                    [&p1, &p2, &pf].into_iter().enumerate() {
                    let mut indices: Vec<u32> =
                        drawn.queries[range.clone()].iter().map(|&u|
                                    if tree == 2 { u / 4 } else { u }).collect();
                    indices.sort();
                    indices.dedup();
                    let nodes = programmed.multiproof(&indices)?;
                    let cap = 32 * compact::SLOT_NODES[3 * batch + tree];
                    if nodes.len() > cap { return Err(Error::Parse); }
                    out.extend_from_slice(&nodes);
                    out.resize(out.len() + cap - nodes.len(), 0);
                }
            }
            if out.len() != compact::PROOF_BYTES { return Err(Error::Parse); }
            let state =
                RefCell::new(CoinState {
                        coins: state.into_inner().coins,
                        next: 0,
                        record: Some(Table::new()),
                        collision: false,
                    });
            let again =
                walk(CoinOracle(&state), &public_bytes, &records, variant)?;
            let state = state.into_inner();
            if again != drawn || state.next != 115 || state.collision {
                return Err(Error::Transcript);
            }
            let (mut table, collision) = table.into_inner();
            if collision { return Err(Error::Merkle); }
            let transcript = state.record.unwrap();
            let transcript_reads = transcript.len();
            for (a, v) in transcript {
                if let Some(p) = table.insert(a, v) {
                    if p != v { return Err(Error::Transcript); }
                }
            }
            times.program = t.elapsed().as_secs_f64();
            times.total = start.elapsed().as_secs_f64();
            return Ok(Simulated {
                        proof: out,
                        table,
                        attempts: k + 1,
                        transcript_reads,
                        commitment_reads: r1 + r2 + rf,
                        times,
                    });
        }
        Err(Error::AttemptsExhausted)
    }
    /// Verify a simulated proof under its programmed oracle (strict tx1 + tx2,
    /// then the dense verifier). Returns (accepted, programmed, read).
    /// Both verifiers parse the adopted compact binary-multiproof format.
    pub fn verify_programmed(public: Public<'_>, proof: &[u8], table: Table)
        -> (Result<(), Error>, usize, usize) {
        install(table);
        let hash: HashFn = programmed_hash;
        let result =
            (||
                        {
                            let public_bytes =
                                crate::host_public::materialize_public_bytes(public).map_err(|_|
                                            Error::Semantic)?;
                            let cp =
                                crate::verifier::tx1(public, &public_bytes, proof,
                                        crate::verifier::SPLIT, LegacyHashFn(hash), None)?;
                            crate::verifier::tx2(&public_bytes, proof, &cp,
                                    LegacyHashFn(hash), None)?;
                            crate::dense::verify(public, proof,
                                    hash).map_err(|_| Error::Relation)
                        })();
        let (programmed, read) = uninstall();
        (result, programmed, read)
    }
}
mod host_sumcheck {
    //! UNPROVED COST PROBE. Isolated semantic interpolation prover.
    use alloc::vec::Vec;
    use aspis_core::field::{WideExact, CM31, M31, QM31};
    use crate::host_wire::{self as wire, Error, SemanticTranscript};
    use aspis_prover::host_arithmetic::evaluate_state_only_polynomial;
    use aspis_core::state_only_sumcheck::state_only_boundary_sum;
    /// R0 keeps all 28 coefficients on the wire, embedded in E. This is the
    /// same interpolation used by the legacy prover, with a new row driver.
    pub(crate) fn interpolate(values: &[QM31; 28]) -> [QM31; 28] {
        let mut out = [QM31::ZERO; 28];
        let mut i = 0;
        while i < 28 {
            let (basis, denominator) = interpolation_basis(i);
            let scale = values[i].mul_m31(denominator.inv());
            out = interpolation_accumulate(out, &basis, scale);
            i += 1;
        }
        out
    }
    fn interpolation_basis(i: usize) -> ([M31; 28], M31) {
        let mut basis = [M31::ZERO; 28];
        basis[0] = M31::ONE;
        interpolation_basis_steps(basis, M31::ONE, 0, i, 0)
    }
    fn interpolation_basis_steps(basis: [M31; 28], denominator: M31,
        degree: usize, i: usize, j: usize) -> ([M31; 28], M31) {
        if j == 28 { return (basis, denominator); }
        if i == j {
            return interpolation_basis_steps(basis, denominator, degree, i,
                    j + 1);
        }
        let basis = interpolation_extend(basis, degree, j);
        let denominator = denominator.mul(M31(i as u32).sub(M31(j as u32)));
        interpolation_basis_steps(basis, denominator, degree + 1, i, j + 1)
    }
    fn interpolation_extend(mut basis: [M31; 28], degree: usize, j: usize)
        -> [M31; 28] {
        let mut k = degree + 2;
        while k > 0 { k -= 1; basis = interpolation_basis_cell(basis, k, j); }
        basis
    }
    fn interpolation_shift(basis: &[M31; 28], k: usize) -> M31 {
        if k == 0 { M31::ZERO } else { basis[k - 1] }
    }
    fn interpolation_basis_cell(mut basis: [M31; 28], k: usize, j: usize)
        -> [M31; 28] {
        let shifted = interpolation_shift(&basis, k);
        let next = shifted.sub(basis[k].mul(M31(j as u32)));
        basis[k] = next;
        basis
    }
    fn interpolation_accumulate(mut out: [QM31; 28], basis: &[M31; 28],
        scale: QM31) -> [QM31; 28] {
        let mut k = 0;
        while k < 28 {
            let value = out[k];
            let delta = scale.mul_m31(basis[k]);
            let next = value.add(delta);
            out[k] = next;
            k += 1;
        }
        out
    }
    pub(crate) trait Oracle: Sync {
        fn evaluate(&self, point: &[QM31; 10])
        -> Result<QM31, Error>;
    }
    pub fn prove_sumcheck<H: aspis_core::Digest32>(transcript:
            &mut SemanticTranscript<H>, output: &mut Vec<u8>,
        initial_claim: QM31, oracle: &impl Oracle)
        -> Result<([QM31; 10], QM31), Error> {
        prove_sumcheck_rounds(transcript, output, [QM31::ZERO; 10],
            initial_claim, 0, oracle)
    }
    fn prove_sumcheck_rounds<H: aspis_core::Digest32,
        F: Oracle>(transcript: &mut SemanticTranscript<H>,
        output: &mut Vec<u8>, point: [QM31; 10], running: QM31, round: usize,
        oracle: &F) -> Result<([QM31; 10], QM31), Error> {
        if round == 10 {
            if oracle.evaluate(&point)? != running {
                return Err(Error::Terminal);
            }
            return Ok((point, running));
        }
        let (point, running) =
            prove_sumcheck_round(transcript, output, point, running, round,
                    oracle)?;
        prove_sumcheck_rounds(transcript, output, point, running, round + 1,
            oracle)
    }
    fn prove_sumcheck_round<H: aspis_core::Digest32,
        F: Oracle>(transcript: &mut SemanticTranscript<H>,
        output: &mut Vec<u8>, mut point: [QM31; 10], mut running: QM31,
        round: usize, oracle: &F) -> Result<([QM31; 10], QM31), Error> {
        let remaining = 9 - round;
        let mut values = [QM31::ZERO; 28];
        {
            let assignments = 1usize << remaining;
            let evaluations =
                crate::host_work::map(100 + round, 28 * assignments,
                    |i|
                        {
                            evaluate_assignment(oracle, point, round, assignments, i)
                        });
            values = merge_evaluations(&evaluations, assignments)?;
        }
        let polynomial = interpolate(&values);
        if state_only_boundary_sum(&polynomial) != running {
            return Err(Error::Boundary { round });
        }
        let polynomial_bytes = encode_polynomial(&polynomial);
        let framed = wire::record(15 + round as u8, &polynomial_bytes)?;
        point[round] = transcript.semantic(15 + round as u8, &framed)?;
        output.extend_from_slice(&framed);
        running = evaluate_state_only_polynomial(&polynomial, point[round]);
        Ok((point, running))
    }
    fn merge_evaluations(evaluations: &[Result<QM31, Error>],
        assignments: usize) -> Result<[QM31; 28], Error> {
        let mut values = [QM31::ZERO; 28];
        let count = evaluations.len();
        let mut i = 0;
        while i < count {
            let value = evaluations[i]?;
            let at = i / assignments;
            let next = values[at].add(value);
            values[at] = next;
            i += 1;
        }
        Ok(values)
    }
    fn evaluate_assignment<F: Oracle>(oracle: &F, point: [QM31; 10],
        round: usize, assignments: usize, i: usize) -> Result<QM31, Error> {
        let remaining = 9 - round;
        let sample = i / assignments;
        let assignment = i % assignments;
        let mut at = point;
        at[round] = QM31::from_cm31(CM31::from_m31(M31(sample as u32)));
        let mut offset = 0;
        while offset < remaining {
            at[round + 1 + offset] =
                if (assignment >> (remaining - 1 - offset)) & 1 == 0 {
                    QM31::ZERO
                } else { QM31::ONE };
            offset += 1;
        }
        oracle.evaluate(&at)
    }
    fn encode_polynomial(polynomial: &[QM31; 28]) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(896);
        let mut i = 0;
        while i < 28 {
            let encoded = WideExact::from_qm31(polynomial[i]).to_le_bytes();
            bytes.extend_from_slice(&encoded);
            i += 1;
        }
        bytes
    }
}
mod host_semantic {
    //! UNPROVED COST PROBE. Own D14 semantic prover; original prover unchanged.
    use crate::prover_helper_sum::state_only_copy_helper_sum;
    use crate::host_multilinear::multilinear_evaluate_qm31;
    use alloc::vec::Vec;
    use crate::host_forest::materialize_copy_helper as build_pool_v1_pair_forest_copy_helper_v1;
    use aspis_core::{
        field::{WideExact, M31, QM31, P},
        Digest32, r0::{domain::Point, encoder::eval_message},
    };
    use crate::host_wire::{
        self as wire, Challenges, Error, SemanticTranscript,
    };
    use aspis_statement::{
        StateOnlyTraceFoundation,
        pool_v1::{
            pair_forest_semantic_terminal::r0::Public,
            pair_forest_trace::PoolV1PairForestMergedC1CompilationV1,
        },
    };
    /// Backend errors abort. Inputs are borrowed only during each call;
    /// no array of column loans survives the call boundary.
    pub trait Commitments {
        fn c1(&mut self, columns: &[Vec<M31>; 26], d: &[QM31; 1024])
        -> Result<[u8; 32], Error>;
        fn c2(&mut self, h1: &[QM31], g: &[QM31; 1024])
        -> Result<[u8; 32], Error>;
    }
    pub struct BuiltSemantics<H: Digest32> {
        pub bytes: Vec<u8>,
        pub transcript: SemanticTranscript<H>,
        pub challenges: Challenges,
        pub alpha: [QM31; 10],
        /// Opening integration starts with this row-25 state, bound roots,
        /// and the 25 challenges (not the later diagnostic row-27 state).
        pub state_before_z0: [u8; 32],
        pub roots: [[u8; 32]; 2],
        pub columns: [Vec<QM31>; 29],
        pub z: [aspis_core::circle::SecureCirclePoint; 2],
    }
    fn lift(x: M31) -> QM31 {
        QM31::from_cm31(aspis_core::field::CM31::from_m31(x))
    }
    pub fn point_claims(columns: &[Vec<QM31>; 29], point: &[QM31; 10])
        -> Result<[[QM31; 29]; 3], Error> {
        let points = wire::statement_points(point);
        let first = claims_at_point(columns, &points[0])?;
        let second = claims_at_point(columns, &points[1])?;
        let third = claims_at_point(columns, &points[2])?;
        Ok([first, second, third])
    }
    #[inline(always)]
    fn claims_at_point(columns: &[Vec<QM31>; 29], point: &[QM31; 10])
        -> Result<[QM31; 29], Error> {
        let mut claims = [QM31::ZERO; 29];
        let mut lane = 0;
        while lane < 29 {
            let value =
                multilinear_evaluate_qm31(&columns[lane],
                            point).ok_or(Error::Public)?;
            claims[lane] = value;
            lane += 1;
        }
        Ok(claims)
    }
    #[allow(clippy::too_many_arguments)]
    fn build_with_helper_mode<H: Digest32>(public: Public<'_>,
        c1: &[Vec<M31>; 26], d: &[QM31; 1024], g: &[QM31; 1024],
        h1_padding: &[QM31; 1024],
        helper: impl FnOnce(QM31, QM31) -> Result<Vec<QM31>, Error>,
        commitments: &mut impl Commitments, hash: H,
        variant: crate::transport::Variant)
        -> Result<BuiltSemantics<H>, Error> {
        check_semantic_columns(c1, d, g)?;
        let c1_root = commitments.c1(c1, d)?;
        let mut transcript =
            SemanticTranscript::new(hash,
                    &crate::host_public::materialize_public_bytes(public).map_err(|_|
                                    Error::Public)?, &c1_root)?;
        let mut bytes = c1_root.to_vec();
        let lambda = semantic_row(0, &[], &mut transcript, &mut bytes)?;
        let chi = semantic_row(1, &[], &mut transcript, &mut bytes)?;
        let mut h1 = helper(lambda, chi)?;
        aspis_prover::state_only_hiding::apply_pool_v1_pair_forest_h1_padding_mask_v1(&mut h1,
                    h1_padding).map_err(|_| Error::Public)?;
        if h1.len() != 1024 { return Err(Error::Public); }
        if state_only_copy_helper_sum(&h1) != Some(QM31::ZERO) {
            return Err(Error::Public);
        }
        let c2_root = commitments.c2(&h1, g)?;
        let theta = semantic_row(2, &c2_root, &mut transcript, &mut bytes)?;
        let zc = zc_rows(&mut transcript, &mut bytes)?;
        let mu = semantic_row(13, &[], &mut transcript, &mut bytes)?;
        let columns = lift_columns(c1, h1, g, d);
        let dc = variant.coefficients(d);
        let mut mask_sum = initial_mask_sum(&columns);
        mask_sum = add_d_tail(mask_sum, &dc);
        let eta =
            semantic_row(14, &WideExact::from_qm31(mask_sum).to_le_bytes(),
                    &mut transcript, &mut bytes)?;
        let challenges = Challenges { lambda, chi, theta, zc, mu, eta };
        let oracle =
            SemanticOracle {
                public: &public,
                columns: &columns,
                challenges: &challenges,
                eta,
                d: &dc,
            };
        let (alpha, _) =
            crate::host_sumcheck::prove_sumcheck(&mut transcript, &mut bytes,
                    mask_sum, &oracle)?;
        let claims = point_claims(&columns, &alpha)?;
        let state_before_z0 = transcript.state();
        let extras = extra_claims(&columns, variant, alpha[8], alpha[9]);
        let before_z0 = wire::record(25, &claim_bytes(claims, extras))?;
        let z0 = transcript.challenge_reference_circle_point(25, &before_z0)?;
        bytes.extend_from_slice(&before_z0);
        let before_z1 =
            wire::record(26, &endpoint_bytes(&columns, variant, z0))?;
        let z1 = transcript.challenge_reference_circle_point(26, &before_z1)?;
        bytes.extend_from_slice(&before_z1);
        if z0 == z1 { return Err(Error::EqualCirclePoints); }
        Ok(BuiltSemantics {
                bytes,
                transcript,
                challenges,
                alpha,
                state_before_z0,
                roots: [c1_root, c2_root],
                columns,
                z: [z0, z1],
            })
    }
    struct SemanticOracle<'a, 'p> {
        public: &'a Public<'p>,
        columns: &'a [Vec<QM31>; 29],
        challenges: &'a Challenges,
        eta: QM31,
        d: &'a [QM31; 1024],
    }
    impl crate::host_sumcheck::Oracle for SemanticOracle<'_, '_> {
        fn evaluate(&self, point: &[QM31; 10]) -> Result<QM31, Error> {
            let claims = point_claims(self.columns, point)?;
            let terminal =
                crate::host_public::terminal_qm31(*self.public, &claims,
                            point, self.challenges).map_err(|_| Error::Public)?;
            let mask = claim_mask_value(claims[0], point);
            Ok(mask.add(self.eta.mul(terminal)).add(extra(self.d, point[8],
                        point[9])))
        }
    }
    fn check_semantic_columns(c1: &[Vec<M31>; 26], d: &[QM31; 1024],
        g: &[QM31; 1024]) -> Result<(), Error> {
        check_base_columns(c1)?;
        check_secure_column(d)?;
        check_secure_column(g)
    }
    fn check_base_columns(c1: &[Vec<M31>; 26]) -> Result<(), Error> {
        let mut lane = 0;
        while lane < 26 { check_base_column(&c1[lane])?; lane += 1; }
        Ok(())
    }
    fn check_base_column(column: &[M31]) -> Result<(), Error> {
        if column.len() != 1024 { return Err(Error::Public); }
        let mut row = 0;
        while row < 1024 {
            if column[row].0 >= P { return Err(Error::Public); }
            row += 1;
        }
        Ok(())
    }
    fn check_secure_column(column: &[QM31; 1024]) -> Result<(), Error> {
        let mut row = 0;
        while row < 1024 {
            let mut b = [0; 16];
            column[row].write_le_bytes(&mut b);
            if QM31::from_le_bytes(&b).is_none() {
                return Err(Error::Public);
            }
            row += 1;
        }
        Ok(())
    }
    fn zc_rows<H: Digest32>(transcript: &mut SemanticTranscript<H>,
        bytes: &mut Vec<u8>) -> Result<[QM31; 10], Error> {
        let mut zc = [QM31::ZERO; 10];
        let mut i = 0;
        while i < 10 {
            zc[i] = semantic_row(3 + i as u8, &[], transcript, bytes)?;
            i += 1;
        }
        Ok(zc)
    }
    fn add_d_tail(mask_sum: QM31, dc: &[QM31; 1024]) -> QM31 {
        let first = d_tail_side(dc, 0).mul_m31(M31(512));
        let mask_sum = mask_sum.add(first);
        let second = d_tail_side(dc, 28).mul_m31(M31(512));
        mask_sum.add(second)
    }
    fn d_tail_side(dc: &[QM31; 1024], offset: usize) -> QM31 {
        d_tail_sum(dc, offset, 0, dc[offset])
    }
    fn d_tail_sum(dc: &[QM31; 1024], offset: usize, j: usize, sum: QM31)
        -> QM31 {
        if j == 28 { return sum; }
        let next = sum.add(dc[offset + j]);
        d_tail_sum(dc, offset, j + 1, next)
    }
    fn lift_columns(c1: &[Vec<M31>; 26], h1: Vec<QM31>, g: &[QM31; 1024],
        d: &[QM31; 1024]) -> [Vec<QM31>; 29] {
        let mut columns: [Vec<QM31>; 29] = Default::default();
        let mut lane = 0;
        while lane < 26 {
            let mut column = Vec::with_capacity(1024);
            let mut row = 0;
            while row < 1024 { column.push(lift(c1[lane][row])); row += 1; }
            columns[lane] = column;
            lane += 1;
        }
        columns[26] = h1;
        columns[27] = g.to_vec();
        columns[28] = d.to_vec();
        columns
    }
    fn boolean_point(row: usize) -> [QM31; 10] {
        let mut point = [QM31::ZERO; 10];
        let mut i = 0;
        while i < 10 {
            point[i] =
                if (row >> (9 - i)) & 1 == 0 {
                    QM31::ZERO
                } else { QM31::ONE };
            i += 1;
        }
        point
    }
    fn initial_mask_sum(columns: &[Vec<QM31>; 29]) -> QM31 {
        let mut sum = QM31::ZERO;
        let mut row = 0;
        while row < 1024 {
            let value = initial_mask_value(columns, row);
            sum = sum.add(value);
            row += 1;
        }
        sum
    }
    fn initial_mask_value(columns: &[Vec<QM31>; 29], row: usize) -> QM31 {
        let point = boolean_point(row);
        let mut semantic = [QM31::ZERO; 16];
        let mut mask_only = [QM31::ZERO; 10];
        let mut i = 0;
        while i < 16 {
            let value = columns[i][row];
            semantic[i] = value;
            i += 1;
        }
        i = 0;
        while i < 10 {
            let value = columns[16 + i][row];
            mask_only[i] = value;
            i += 1;
        }
        aspis_prover::host_arithmetic::state_only_selected_mask_value(&semantic,
            &mask_only, columns[27][row], &point)
    }
    fn claim_mask_value(claims: [QM31; 29], point: &[QM31; 10]) -> QM31 {
        let mut semantic = [QM31::ZERO; 16];
        let mut mask_only = [QM31::ZERO; 10];
        semantic.copy_from_slice(&claims[..16]);
        mask_only.copy_from_slice(&claims[16..26]);
        aspis_prover::host_arithmetic::state_only_selected_mask_value(&semantic,
            &mask_only, claims[27], point)
    }
    fn column_coefficients(column: &[QM31],
        variant: crate::transport::Variant) -> [QM31; 1024] {
        let rows: &[QM31; 1024] = column.try_into().unwrap();
        variant.coefficients(rows)
    }
    fn extra_claims(columns: &[Vec<QM31>; 29],
        variant: crate::transport::Variant, a: QM31, b: QM31) -> [QM31; 29] {
        let mut extras = [QM31::ZERO; 29];
        let mut lane = 0;
        while lane < 29 {
            let coefficients = column_coefficients(&columns[lane], variant);
            let value = extra(&coefficients, a, b);
            extras[lane] = value;
            lane += 1;
        }
        extras
    }
    fn claim_bytes(claims: [[QM31; 29]; 3], extras: [QM31; 29]) -> Vec<u8> {
        let bytes = Vec::with_capacity(3712);
        let bytes = append_claim_bytes(bytes, &claims[0]);
        let bytes = append_claim_bytes(bytes, &claims[1]);
        let bytes = append_claim_bytes(bytes, &claims[2]);
        append_claim_bytes(bytes, &extras)
    }
    fn append_claim_bytes(mut bytes: Vec<u8>, claims: &[QM31; 29])
        -> Vec<u8> {
        let mut lane = 0;
        while lane < 29 {
            let encoded = WideExact::from_qm31(claims[lane]).to_le_bytes();
            bytes.extend_from_slice(&encoded);
            lane += 1;
        }
        bytes
    }
    fn endpoint_bytes(columns: &[Vec<QM31>; 29],
        variant: crate::transport::Variant,
        z: aspis_core::circle::SecureCirclePoint) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(928);
        let mut lane = 0;
        while lane < 29 {
            let coefficients = column_coefficients(&columns[lane], variant);
            let value = eval_message(&coefficients, Point { x: z.x, y: z.y });
            bytes.extend_from_slice(&WideExact::from_qm31(value).to_le_bytes());
            lane += 1;
        }
        bytes
    }
    pub fn extra(coefficients: &[QM31; 1024], a: QM31, b: QM31) -> QM31 {
        let mut sum = QM31::ZERO;
        let mut side = 0;
        while side < 2 {
            let mut value = QM31::ZERO;
            let x = if side == 0 { a } else { b };
            let mut j = 28;
            while j > 0 {
                j -= 1;
                value = value.mul(x).add(coefficients[28 * side + j]);
            }
            sum = sum.add(value);
            side += 1;
        }
        sum
    }
    /// One transcript transition, with no captured mutable state.
    fn semantic_row<H: Digest32>(row: u8, payload: &[u8],
        transcript: &mut SemanticTranscript<H>, bytes: &mut Vec<u8>)
        -> Result<QM31, Error> {
        let framed = wire::record(row, payload)?;
        let value = transcript.semantic(row, &framed)?;
        bytes.extend_from_slice(&framed);
        Ok(value)
    }
    pub fn build<H: Digest32>(public: Public<'_>,
        compiled: &PoolV1PairForestMergedC1CompilationV1,
        mask_only: &[Vec<M31>; 10], d: &[QM31; 1024], g: &[QM31; 1024],
        commitments: &mut impl Commitments, hash: H,
        variant: crate::transport::Variant)
        -> Result<BuiltSemantics<H>, Error> {
        if compiled.semantic_c1.c1.len() != 16 ||
                &compiled.public_statement != public.transition() {
            return Err(Error::Public);
        }
        let c1 =
            core::array::from_fn(|i|
                    if i < 16 {
                        compiled.semantic_c1.c1[i].clone()
                    } else { mask_only[i - 16].clone() });
        build_with_helper_mode(public, &c1, d, g, &[QM31::ZERO; 1024],
            |lambda, chi|
                build_pool_v1_pair_forest_copy_helper_v1(&compiled.trace,
                        public.transition().live_snapshot.next_pair_index, lambda,
                        chi).map_err(|_| Error::Public), commitments, hash, variant)
    }
    /// Real and fixture entry for C1/H1 material from the state-only mask
    /// APIs. The compiled trace remains the helper source; only the semantic C1
    /// input is replaced with its independently masked clone.
    pub fn build_with_material<H: Digest32>(public: Public<'_>,
        compiled: &PoolV1PairForestMergedC1CompilationV1,
        noised_semantic_c1: &StateOnlyTraceFoundation,
        mask_only: &[Vec<M31>; 10], d: &[QM31; 1024], g: &[QM31; 1024],
        h1_padding: &[QM31; 1024], commitments: &mut impl Commitments,
        hash: H, variant: crate::transport::Variant)
        -> Result<BuiltSemantics<H>, Error> {
        if noised_semantic_c1.c1.len() != 16 ||
                    compiled.semantic_c1.c1.len() != 16 ||
                &compiled.public_statement != public.transition() {
            return Err(Error::Public);
        }
        let c1 = clone_semantic_columns(&noised_semantic_c1.c1, mask_only);
        build_with_helper_mode(public, &c1, d, g, h1_padding,
            |lambda, chi|
                {
                    if !no_pole(compiled, lambda, chi)? {
                        return Err(Error::ActivePole);
                    }
                    build_pool_v1_pair_forest_copy_helper_v1(&compiled.trace,
                            public.transition().live_snapshot.next_pair_index, lambda,
                            chi).map_err(|_| Error::Public)
                }, commitments, hash, variant)
    }
    fn clone_semantic_columns(noised: &[Vec<M31>], mask_only: &[Vec<M31>; 10])
        -> [Vec<M31>; 26] {
        let mut c1: [Vec<M31>; 26] = Default::default();
        let mut i = 0;
        while i < 16 { c1[i] = noised[i].clone(); i += 1; }
        while i < 26 { c1[i] = mask_only[i - 16].clone(); i += 1; }
        c1
    }
    /// Lean `NoPole (h.build w) λ χ` (R0Z/HonestValidity.lean:97–99), the `VR1`
    /// conjunct of `realGameP` (R1Z/GamesR1P.lean:184): on every copy-active row,
    /// chi differs from all four slot values (producer and consumer, slots 0 and
    /// 1), whatever the slot's weight; an unused slot has value 0. The weighted
    /// slots `build_copy_logup_helper` inverts are a subset, so this check is
    /// stronger than its `ActivePole`. Only the verdict leaves this function.
    pub(crate) fn no_pole(compiled: &PoolV1PairForestMergedC1CompilationV1,
        lambda: QM31, chi: QM31) -> Result<bool, Error> {
        let values = lean_copy_row_values(&compiled.trace, lambda)?;
        let masks =
            crate::host_forest::pool_v1_pair_forest_copy_active_row_masks_v1().map_err(|_|
                        Error::Public)?;
        return Ok(crate::ct_pole::all_slots_clear(&values, &masks, chi));
    }
    /// Lean `copyRowValues t λ b endpoint slot` (v8-r0-sem-proof-20261008
    /// lean/R0P/Copy.lean:449–452) for every row b, side (0 producer, 1 consumer)
    /// and slot: the sum of the compressed tuples of the registry endpoints at
    /// that row, side and static slot, weights ignored. The static slot is the
    /// endpoint's position among the registry endpoints on the same row and side,
    /// which is the slot of the generated terminal constants that the Lean
    /// `copyLinks` transcribe (`retry_tests::static_slots_are_the_terminal_constants`).
    /// The prover's `pool_v1_pair_forest_copy_rows_v1` cannot be used here: it
    /// places an endpoint in the first slot whose weight is zero, so a zero-weight
    /// endpoint followed by another on the same row and side is overwritten.
    pub(crate) fn lean_copy_row_values(trace:
            &aspis_statement::pool_v1::pair_forest_trace::PoolV1PairForestTraceV1,
        lambda: QM31) -> Result<Vec<[[QM31; 2]; 2]>, Error> {
        let registry =
            crate::host_forest::build_pool_v1_pair_forest_copy_registry_v1().map_err(|_|
                        Error::Public)?;
        let mut values = ::alloc::vec::from_elem([[QM31::ZERO; 2]; 2], 1024);
        let mut arity = ::alloc::vec::from_elem([0usize; 2], 1024);
        let count = registry.len;
        let mut index = 0;
        while index < count {
            let link = registry.data[index];
            (values, arity) =
                copy_endpoint_values(trace, link.producer, link.tag, lambda,
                        0, values, arity)?;
            (values, arity) =
                copy_endpoint_values(trace, link.consumer, link.tag, lambda,
                        1, values, arity)?;
            index += 1;
        }
        Ok(values)
    }
    fn copy_endpoint_values(trace:
            &aspis_statement::pool_v1::pair_forest_trace::PoolV1PairForestTraceV1,
        tuple: aspis_statement::pool_v1::pair_trace::PoolV1PairCopyTupleV1,
        tag: M31, lambda: QM31, side: usize, mut values: Vec<[[QM31; 2]; 2]>,
        mut arity: Vec<[usize; 2]>)
        -> Result<(Vec<[[QM31; 2]; 2]>, Vec<[usize; 2]>), Error> {
        let row = usize::from(tuple.row);
        if row >= 1024 || arity[row][side] >= 2 { return Err(Error::Public); }
        let slot = arity[row][side];
        arity[row][side] += 1;
        let limbs = copy_tuple_values(trace, tuple)?;
        let compressed =
            crate::prover_shared::compress_tagged_tuple(tag, &limbs, lambda);
        let next = values[row][side][slot].add(compressed);
        values[row][side][slot] = next;
        Ok((values, arity))
    }
    fn copy_tuple_values(trace:
            &aspis_statement::pool_v1::pair_forest_trace::PoolV1PairForestTraceV1,
        tuple: aspis_statement::pool_v1::pair_trace::PoolV1PairCopyTupleV1)
        -> Result<[M31; 16], Error> {
        Ok([copy_tuple_limb(trace, tuple.limbs[0])?,
                    copy_tuple_limb(trace, tuple.limbs[1])?,
                    copy_tuple_limb(trace, tuple.limbs[2])?,
                    copy_tuple_limb(trace, tuple.limbs[3])?,
                    copy_tuple_limb(trace, tuple.limbs[4])?,
                    copy_tuple_limb(trace, tuple.limbs[5])?,
                    copy_tuple_limb(trace, tuple.limbs[6])?,
                    copy_tuple_limb(trace, tuple.limbs[7])?,
                    copy_tuple_limb(trace, tuple.limbs[8])?,
                    copy_tuple_limb(trace, tuple.limbs[9])?,
                    copy_tuple_limb(trace, tuple.limbs[10])?,
                    copy_tuple_limb(trace, tuple.limbs[11])?,
                    copy_tuple_limb(trace, tuple.limbs[12])?,
                    copy_tuple_limb(trace, tuple.limbs[13])?,
                    copy_tuple_limb(trace, tuple.limbs[14])?,
                    copy_tuple_limb(trace, tuple.limbs[15])?])
    }
    fn copy_tuple_limb(trace:
            &aspis_statement::pool_v1::pair_forest_trace::PoolV1PairForestTraceV1,
        limb: aspis_statement::pool_v1::pair_trace::PoolV1PairTupleLimbV1)
        -> Result<M31, Error> {
        use aspis_statement::pool_v1::pair_trace::{
            PoolV1PairTraceBankV1, PoolV1PairTupleLimbV1,
        };
        match limb {
            PoolV1PairTupleLimbV1::Zero => Ok(M31::ZERO),
            PoolV1PairTupleLimbV1::Cell { source, offset } => {
                let column = source.cell.column as usize;
                let row = source.cell.row as usize;
                match source.bank {
                    PoolV1PairTraceBankV1::Stable =>
                        copy_cell(&trace.stable.c1, column, row, offset),
                    PoolV1PairTraceBankV1::Late =>
                        copy_cell(&trace.late, column, row, offset),
                }
            }
        }
    }
    fn copy_cell(columns: &[Vec<M31>], column: usize, row: usize, offset: M31)
        -> Result<M31, Error> {
        if column >= columns.len() || row >= columns[column].len() {
            return Err(Error::Public);
        }
        Ok(columns[column][row].add(offset))
    }
}
mod host_commitment {
    //! UNPROVED COST PROBE. Isolated packed commitments and native encoder.
    use alloc::vec::Vec;
    use aspis_core::{
        HashFn, field::{WideExact as E, M31, QM31},
        r0::{
            domain::{self, FibreIndex, Point},
            fold, merkle, wire::FibreOpening, opening::LANES, heap::filled,
            CodeField, Error, Message, FIBRE_COUNT, WORD_LEN,
        },
    };
    /// Natural-product evaluation tree. Coordinates are always in F.
    pub struct EncodingDomain {
        xy: Vec<Point<M31>>,
        levels: Vec<Vec<M31>>,
    }
    impl EncodingDomain {
        pub fn new() -> Result<Self, Error> {
            let xy = domain_points()?;
            let mut levels = Vec::new();
            levels.try_reserve_exact(9).map_err(|_| Error::Allocation)?;
            let first = domain_first_level(&xy)?;
            levels.push(first);
            let levels = domain_append_levels(levels, 0)?;
            Ok(Self { xy, levels })
        }
        pub fn evaluate<T: CodeField>(&self, coefficients: &[T], depth: usize)
            -> Result<Vec<T>, Error> {
            let count = self.levels[depth].len();
            if coefficients.len() == 1 {
                return filled(count, coefficients[0]);
            }
            let (even, odd) = split_coefficients(coefficients)?;
            let a = self.evaluate(&even, depth + 1)?;
            let b = self.evaluate(&odd, depth + 1)?;
            merge_evaluations(&self.levels[depth], &a, &b)
        }
        /// Exact §3 encoder at every stored index, O(N log 1024), using
        /// N_(2j)(x)=N_j(2x²−1), N_(2j+1)(x)=x*N_j(2x²−1).
        pub fn encode<T: CodeField>(&self, message: &Message<T>)
            -> Result<Vec<T>, Error> {
            let mut channels = Vec::new();
            channels.try_reserve_exact(4).map_err(|_| Error::Allocation)?;
            let first = self.encode_channel(message, 0)?;
            channels.push(first);
            let second = self.encode_channel(message, 1)?;
            channels.push(second);
            let third = self.encode_channel(message, 2)?;
            channels.push(third);
            let fourth = self.encode_channel(message, 3)?;
            channels.push(fourth);
            let mut word = filled(WORD_LEN, T::ZERO)?;
            let count = self.xy.len();
            let mut u = 0;
            while u < count {
                let values = encode_fibre(self.xy[u], &channels, u);
                word[4 * u..4 * u + 4].copy_from_slice(&values);
                u += 1;
            }
            Ok(word)
        }
        fn encode_channel<T: CodeField>(&self, message: &Message<T>, s: usize)
            -> Result<Vec<T>, Error> {
            let mut coefficients = [T::ZERO; 256];
            let mut d = 0;
            while d < 256 {
                let value = message[4 * d + s];
                coefficients[d] = value;
                d += 1;
            }
            self.evaluate(&coefficients, 0)
        }
    }
    fn encode_fibre<T: CodeField>(point: Point<M31>, channels: &[Vec<T>],
        u: usize) -> [T; 4] {
        let x = T::from_m31(point.x);
        let y = T::from_m31(point.y);
        let values =
            [channels[0][u], channels[1][u], channels[2][u], channels[3][u]];
        fold::phi_inverse(x, y, values)
    }
    fn split_coefficients<T: CodeField>(coefficients: &[T])
        -> Result<(Vec<T>, Vec<T>), Error> {
        let mut even = filled(coefficients.len() / 2, T::ZERO)?;
        let mut odd = filled(even.len(), T::ZERO)?;
        let mut j = 0;
        while j < even.len() {
            even[j] = coefficients[2 * j];
            odd[j] = coefficients[2 * j + 1];
            j += 1;
        }
        Ok((even, odd))
    }
    fn merge_evaluations<T: CodeField>(nodes: &[M31], a: &[T], b: &[T])
        -> Result<Vec<T>, Error> {
        let mut out = filled(nodes.len(), T::ZERO)?;
        let mut j = 0;
        while j < nodes.len() {
            out[j] = a[j / 2].add(T::from_m31(nodes[j]).mul(b[j / 2]));
            j += 1;
        }
        Ok(out)
    }
    fn domain_points() -> Result<Vec<Point<M31>>, Error> {
        let count = FIBRE_COUNT;
        let mut xy = filled(count, Point { x: M31::ZERO, y: M31::ZERO })?;
        let mut u = 0;
        while u < count {
            xy[u] = domain::fibre_point(FibreIndex::new(u)?);
            u += 1;
        }
        Ok(xy)
    }
    fn domain_first_level(xy: &[Point<M31>]) -> Result<Vec<M31>, Error> {
        let count = FIBRE_COUNT;
        let mut first = filled(FIBRE_COUNT, M31::ZERO)?;
        let mut u = 0;
        while u < count {
            first[u] = xy[u].x.mul(xy[u].x).double().sub(M31::ONE);
            u += 1;
        }
        Ok(first)
    }
    fn domain_next_level(previous: &[M31]) -> Result<Vec<M31>, Error> {
        let mut next = filled(previous.len() / 2, M31::ZERO)?;
        let mut j = 0;
        while j < next.len() {
            next[j] =
                previous[2 * j].mul(previous[2 * j]).double().sub(M31::ONE);
            j += 1;
        }
        Ok(next)
    }
    /// Structural recursion moves the level owner; no level loan crosses a loop join.
    fn domain_append_levels(mut levels: Vec<Vec<M31>>, depth: usize)
        -> Result<Vec<Vec<M31>>, Error> {
        if depth == 8 { return Ok(levels); }
        let next = domain_next_level(&levels[depth])?;
        levels.push(next);
        domain_append_levels(levels, depth + 1)
    }
    pub enum CommitmentTime { C1, C2, }
    #[automatically_derived]
    #[doc(hidden)]
    unsafe impl ::core::clone::TrivialClone for CommitmentTime { }
    #[automatically_derived]
    impl ::core::clone::Clone for CommitmentTime {
        #[inline]
        fn clone(&self) -> CommitmentTime { *self }
    }
    #[automatically_derived]
    impl ::core::marker::Copy for CommitmentTime { }
    #[automatically_derived]
    impl ::core::fmt::Debug for CommitmentTime {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            ::core::fmt::Formatter::write_str(f,
                match self {
                    CommitmentTime::C1 => "C1",
                    CommitmentTime::C2 => "C2",
                })
        }
    }
    #[automatically_derived]
    impl ::core::marker::StructuralPartialEq for CommitmentTime { }
    #[automatically_derived]
    impl ::core::cmp::PartialEq for CommitmentTime {
        #[inline]
        fn eq(&self, other: &CommitmentTime) -> bool {
            let __self_discr = ::core::intrinsics::discriminant_value(self);
            let __arg1_discr = ::core::intrinsics::discriminant_value(other);
            __self_discr == __arg1_discr
        }
    }
    #[automatically_derived]
    impl ::core::cmp::Eq for CommitmentTime {
        #[inline]
        #[doc(hidden)]
        #[coverage(off)]
        fn assert_fields_are_eq(&self) {}
    }
    enum Word { Base(Vec<M31>), Secure(Vec<QM31>), }
    impl Word {
        fn value(&self, i: usize) -> E {
            match self {
                Self::Base(w) => E::from_m31(w[i]),
                Self::Secure(w) => E::from_qm31(w[i]),
            }
        }
    }
    /// C1 can be constructed before λ/χ; C2 separately after them. The 29-entry
    /// input permits virtual lanes but only this time's lanes are committed.
    pub struct Commitment {
        time: CommitmentTime,
        lanes: Vec<usize>,
        words: Vec<Word>,
        /// Binary tree of the adopted format (PREREG-PROOF-SIZE-2). The eight-way
        /// tree is retired: a prover build cannot emit an eight-way proof.
        tree: crate::host_tree::BinaryTree,
        private_salts: Option<PrivateSalts>,
    }
    /// Host-only secret salts retained until queried openings have been emitted.
    /// Drop overwrites the full salt buffer so salts for unopened leaves are not
    /// left in the allocator after proof construction.
    pub struct PrivateSalts(Vec<[u8; 32]>);
    impl PrivateSalts {
        pub fn new(values: Vec<[u8; 32]>) -> Self { Self(values) }
        pub fn get(&self, index: usize) -> &[u8; 32] { &self.0[index] }
        fn len(&self) -> usize { self.0.len() }
    }
    #[inline(always)]
    pub(crate) fn clear_private_salt(salt: &mut [u8; 32]) {
        unsafe { core::ptr::write_volatile(salt, [0; 32]); }
    }
    impl Drop for PrivateSalts {
        fn drop(&mut self) {
            let mut index = 0;
            while index < self.0.len() {
                clear_private_salt(&mut self.0[index]);
                index += 1;
            }
            core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
        }
    }
    impl Commitment {
        pub fn new_salted(hash: HashFn, domain: &EncodingDomain,
            time: CommitmentTime, messages: &[Message<E>],
            variant: crate::transport::Variant, salts: PrivateSalts)
            -> Result<Self, Error> {
            Self::build(hash, domain, time, messages, variant, Some(salts))
        }
        fn build(hash: HashFn, domain: &EncodingDomain, time: CommitmentTime,
            messages: &[Message<E>], variant: crate::transport::Variant,
            private_salts: Option<PrivateSalts>) -> Result<Self, Error> {
            if messages.len() != LANES { return Err(Error::WrongLength); }
            if private_salts.as_ref().is_some_and(|salts|
                        salts.len() != FIBRE_COUNT) {
                return Err(Error::WrongLength);
            }
            let lanes = commitment_lanes(time)?;
            let words =
                encode_commitment_words(domain, messages, variant, &lanes)?;
            let leaves =
                commitment_leaves(hash, time, &lanes, &words,
                        private_salts.as_ref())?;
            Ok(Self {
                    time,
                    lanes,
                    words,
                    tree: crate::host_tree::BinaryTree::new(aspis_core::digest::LegacyHashFn(hash),
                                leaves).ok_or(Error::WrongLength)?,
                    private_salts,
                })
        }
        pub fn root(&self) -> [u8; 32] { self.tree.root() }
        /// Binary multiproof for strictly increasing indices.
        pub(crate) fn multiproof(&self, indices: &[u32]) -> Option<Vec<u8>> {
            self.tree.multiproof(indices)
        }
        pub(crate) fn fill_opening(&self, u: FibreIndex,
            out: &mut FibreOpening) {
            out.values = fill_opening_values(self, u, out.values, 0);
            let path = opening_path(self.time);
            out.paths[path] = [[[0; 32]; 7]; 6];
        }
        pub(crate) fn opening_salt(&self, u: FibreIndex)
            -> Option<&[u8; 32]> {
            match &self.private_salts {
                Some(salts) => Some(salts.get(u.get())),
                None => None,
            }
        }
    }
    fn commitment_lanes(time: CommitmentTime) -> Result<Vec<usize>, Error> {
        match time {
            CommitmentTime::C1 => {
                let mut lanes = filled(27, 0)?;
                lanes.copy_from_slice(&[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11,
                                12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
                                28]);
                Ok(lanes)
            }
            CommitmentTime::C2 => {
                let mut lanes = filled(2, 0)?;
                lanes.copy_from_slice(&[26, 27]);
                Ok(lanes)
            }
        }
    }
    fn validate_commitment_lanes(messages: &[Message<E>], lanes: &[usize])
        -> Result<(), Error> {
        let mut i = 0;
        while i < lanes.len() {
            validate_lane(&messages[lanes[i]], lanes[i])?;
            i += 1;
        }
        Ok(())
    }
    fn encode_commitment_words(domain: &EncodingDomain,
        messages: &[Message<E>], variant: crate::transport::Variant,
        lanes: &[usize]) -> Result<Vec<Word>, Error> {
        let mut words = Vec::new();
        words.try_reserve_exact(lanes.len()).map_err(|_| Error::Allocation)?;
        {
            validate_commitment_lanes(messages, lanes)?;
            let encoded =
                crate::host_work::map(200, lanes.len(),
                    |i|
                        {
                            encode_commitment_lane(domain, messages, variant, lanes[i])
                        });
            let mut encoded = encoded;
            let mut i = 0;
            while i < encoded.len() / 2 {
                let j = encoded.len() - 1 - i;
                encoded.swap(i, j);
                i += 1;
            }
            while !encoded.is_empty() {
                let word = encoded.pop().unwrap()?;
                words.push(word);
            }
        }
        Ok(words)
    }
    fn encode_commitment_lane(domain: &EncodingDomain,
        messages: &[Message<E>], variant: crate::transport::Variant,
        lane: usize) -> Result<Word, Error> {
        let coefficients = variant.coefficients(&messages[lane]);
        if lane < 26 {
            let base = base_coefficients(&coefficients);
            Ok(Word::Base(domain.encode(&base)?))
        } else {
            let secure = secure_coefficients(&coefficients);
            Ok(Word::Secure(domain.encode(&secure)?))
        }
    }
    fn base_coefficients(coefficients: &Message<E>) -> Message<M31> {
        let mut out = [M31::ZERO; 1024];
        let mut i = 0;
        while i < 1024 {
            let value = M31(coefficients[i].to_limbs()[0]);
            out[i] = value;
            i += 1;
        }
        out
    }
    fn secure_coefficients(coefficients: &Message<E>) -> Message<QM31> {
        let mut out = [QM31::ZERO; 1024];
        let mut i = 0;
        while i < 1024 {
            let value = coefficients[i].c0();
            out[i] = value;
            i += 1;
        }
        out
    }
    fn commitment_leaves(hash: HashFn, time: CommitmentTime, lanes: &[usize],
        words: &[Word], private_salts: Option<&PrivateSalts>)
        -> Result<Vec<[u8; 32]>, Error> {
        let leaves = filled(FIBRE_COUNT, [0; 32])?;
        let tag = commitment_tag(time);
        let leaves =
            match private_salts {
                Some(salts) =>
                    salted_commitment_leaves(hash, tag, lanes, words, salts,
                        leaves),
                None =>
                    plain_commitment_leaves(hash, tag, lanes, words, leaves),
            };
        Ok(leaves)
    }
    fn commitment_tag(time: CommitmentTime) -> u8 {
        match time {
            CommitmentTime::C1 => merkle::C1_TAG,
            CommitmentTime::C2 => merkle::C2_TAG,
        }
    }
    fn salted_commitment_leaves(hash: HashFn, tag: u8, lanes: &[usize],
        words: &[Word], salts: &PrivateSalts, mut leaves: Vec<[u8; 32]>)
        -> Vec<[u8; 32]> {
        let count = leaves.len();
        let mut u = 0;
        while u < count {
            let (bytes, at) = commitment_leaf_bytes(words, lanes, u);
            let salt = salts.get(u);
            let leaf =
                aspis_core::state_only_private_merkle::private_leaf_hash(hash,
                    tag, &bytes[..at], salt);
            leaves[u] = leaf;
            u += 1;
        }
        leaves
    }
    fn plain_commitment_leaves(hash: HashFn, tag: u8, lanes: &[usize],
        words: &[Word], mut leaves: Vec<[u8; 32]>) -> Vec<[u8; 32]> {
        let count = leaves.len();
        let mut u = 0;
        while u < count {
            let (bytes, at) = commitment_leaf_bytes(words, lanes, u);
            let leaf = merkle::leaf(hash, tag, &bytes[..at]);
            leaves[u] = leaf;
            u += 1;
        }
        leaves
    }
    fn commitment_leaf_bytes(words: &[Word], lanes: &[usize], u: usize)
        -> ([u8; 480], usize) {
        let mut bytes = [0u8; 480];
        let mut at = 0;
        let mut s = 0;
        while s < 4 {
            let mut j = 0;
            while j < lanes.len() {
                let b = words[j].value(4 * u + s).to_le_bytes();
                let width = if lanes[j] < 26 { 4 } else { 16 };
                bytes[at..at + width].copy_from_slice(&b[..width]);
                at += width;
                j += 1;
            }
            s += 1;
        }
        (bytes, at)
    }
    fn validate_lane(message: &Message<E>, lane: usize) -> Result<(), Error> {
        let first = if lane < 26 { 1 } else { 4 };
        let mut row = 0;
        while row < 1024 {
            let limbs = message[row].to_limbs();
            validate_zero_tail(&limbs, first)?;
            row += 1;
        }
        Ok(())
    }
    fn validate_zero_tail(limbs: &[u32; 8], mut i: usize)
        -> Result<(), Error> {
        while i < 8 {
            if limbs[i] != 0 { return Err(Error::WrongField); }
            i += 1;
        }
        Ok(())
    }
    fn opening_lane_values(word: &Word, u: FibreIndex) -> [E; 4] {
        let at = 4 * u.get();
        [word.value(at), word.value(at + 1), word.value(at + 2),
                word.value(at + 3)]
    }
    fn fill_opening_values(c: &Commitment, u: FibreIndex,
        mut values: [[E; 29]; 4], j: usize) -> [[E; 29]; 4] {
        if j == c.lanes.len() { return values; }
        let lane = c.lanes[j];
        let row = opening_lane_values(&c.words[j], u);
        values[0][lane] = row[0];
        values[1][lane] = row[1];
        values[2][lane] = row[2];
        values[3][lane] = row[3];
        fill_opening_values(c, u, values, j + 1)
    }
    fn opening_path(time: CommitmentTime) -> usize {
        match time { CommitmentTime::C1 => 0, CommitmentTime::C2 => 1, }
    }
}
mod host_tree {
    //! Owned host tree driver. Parent hashing is the unchanged framed leaf kernel.
    use alloc::vec::Vec;
    use aspis_core::Digest32;
    use crate::multiproof::{binary_parent, LEAF_BITS, MAX_BATCH};
    pub(crate) struct BinaryTree {
        levels: Vec<Vec<[u8; 32]>>,
    }
    impl BinaryTree {
        pub(crate) fn new<H: Digest32>(hash: H, leaves: Vec<[u8; 32]>)
            -> Option<Self> {
            if leaves.len() != 1 << LEAF_BITS { return None; }
            let mut levels = Vec::with_capacity(LEAF_BITS as usize + 1);
            levels.push(leaves);
            let levels = append_levels(hash, levels, 0);
            Some(Self { levels })
        }
        pub(crate) fn root(&self) -> [u8; 32] {
            self.levels[LEAF_BITS as usize][0]
        }
        pub(crate) fn multiproof(&self, indices: &[u32]) -> Option<Vec<u8>> {
            let bits = LEAF_BITS as usize;
            let count = node_count(indices)?;
            let out = Vec::with_capacity(32 * count);
            let level = indices.to_vec();
            let out = multiproof_levels(self, out, level, 0, bits);
            if out.len() == 32 * count { Some(out) } else { None }
        }
    }
    fn multiproof_levels(tree: &BinaryTree, out: Vec<u8>, level: Vec<u32>,
        depth: usize, bits: usize) -> Vec<u8> {
        if depth == bits { return out; }
        let (out, next) = multiproof_level(&tree.levels[depth], &level, out);
        drop(level);
        multiproof_levels(tree, out, next, depth + 1, bits)
    }
    fn multiproof_level(nodes: &[[u8; 32]], level: &[u32], mut out: Vec<u8>)
        -> (Vec<u8>, Vec<u32>) {
        let mut next = Vec::new();
        let count = level.len();
        let mut i = 0;
        while i < count {
            let parent = level[i] >> 1;
            (out, i) = multiproof_child(nodes, level, out, i, parent << 1);
            (out, i) =
                multiproof_child(nodes, level, out, i, (parent << 1) | 1);
            next.push(parent);
        }
        (out, next)
    }
    fn multiproof_child(nodes: &[[u8; 32]], level: &[u32], mut out: Vec<u8>,
        i: usize, child: u32) -> (Vec<u8>, usize) {
        if i < level.len() && level[i] == child {
            (out, i + 1)
        } else { out.extend_from_slice(&nodes[child as usize]); (out, i) }
    }
    fn next_level<H: Digest32>(hash: H, previous: &[[u8; 32]])
        -> Vec<[u8; 32]> {
        let n = previous.len() / 2;
        let mut next = Vec::with_capacity(n);
        let mut i = 0;
        while i < n {
            let parent =
                binary_parent(hash, &previous[2 * i], &previous[2 * i + 1]);
            next.push(parent);
            i += 1;
        }
        next
    }
    fn append_levels<H: Digest32>(hash: H, mut levels: Vec<Vec<[u8; 32]>>,
        depth: usize) -> Vec<Vec<[u8; 32]>> {
        if depth == LEAF_BITS as usize { return levels; }
        let next = next_level(hash, &levels[depth]);
        levels.push(next);
        append_levels(hash, levels, depth + 1)
    }
    fn check_indices(indices: &[u32]) -> Option<()> {
        if indices.is_empty() || indices.len() > MAX_BATCH { return None; }
        let mut i = 0;
        while i < indices.len() {
            if indices[i] >= 1 << LEAF_BITS ||
                    (i > 0 && indices[i - 1] >= indices[i]) {
                return None;
            }
            i += 1;
        }
        Some(())
    }
    fn node_count(indices: &[u32]) -> Option<usize> {
        check_indices(indices)?;
        let mut level = [0u32; MAX_BATCH];
        level[..indices.len()].copy_from_slice(indices);
        Some(count_levels(level, indices.len(), 0, 0, LEAF_BITS))
    }
    fn count_levels(level: [u32; MAX_BATCH], n: usize, depth: u32,
        count: usize, bits: u32) -> usize {
        if depth == bits { return count; }
        let (level, n, missing) = count_level(level, n);
        count_levels(level, n, depth + 1, count + missing, bits)
    }
    fn count_level(mut level: [u32; MAX_BATCH], n: usize)
        -> ([u32; MAX_BATCH], usize, usize) {
        let mut i = 0;
        let mut w = 0;
        let mut missing = 0;
        while i < n {
            let (parent, take) = count_parent(&level, i, n);
            level[w] = parent;
            w += 1;
            i += take;
            missing += 2 - take;
        }
        (level, w, missing)
    }
    fn count_parent(level: &[u32; MAX_BATCH], i: usize, n: usize)
        -> (u32, usize) {
        let parent = level[i] >> 1;
        let take =
            if i + 1 < n && level[i + 1] >> 1 == parent { 2 } else { 1 };
        (parent, take)
    }
}
mod host_transcript {
    //! Host-only counted opening transcript and ordered query scanner.
    use aspis_core::r0::CodeField;
    use aspis_core::{Digest32, field::WideExact as E};
    use crate::transport::Variant;
    pub struct Transcript<H: Digest32> {
        pub state: [u8; 32],
        hash: H,
    }
    impl<H: Digest32> Transcript<H> {
        pub fn new(hash: H, semantic_state: [u8; 32], variant: Variant)
            -> Self {
            let domain: &[u8] = b"UNPROVED:R1:PRIVATE-SALTED:P3";
            Self {
                state: hash.digest(&[domain, &[variant.tag()],
                                &semantic_state]),
                hash,
            }
        }
        pub fn absorb(&mut self, row: u8, payload: &[u8]) {
            self.state =
                self.hash.digest(&[&self.state, &[0, 0xa0 + row],
                                &(payload.len() as u32).to_le_bytes(), payload]);
        }
        pub fn block(&mut self, row: u8, payload: &[u8]) -> [u8; 32] {
            self.absorb(row, payload);
            let block = self.hash.digest(&[&self.state, &[1]]);
            self.state = self.hash.digest(&[&self.state, &[2]]);
            block
        }
        pub fn scalar(&mut self, row: u8, payload: &[u8], nonzero: bool)
            -> E {
            let block = self.block(row, payload);
            let out =
                if nonzero {
                    crate::host_sampler::gamma_sample(&block)
                } else { crate::host_sampler::ordinary_sample(&block) };
            crate::trace::value(4, row as usize, out);
            out
        }
        /// Final query-residual batching: at most 22 coefficients, so a nonzero
        /// residual has at most 21 roots even when sampled from the K subfield.
        /// Gamma and both folding challenges continue to use E.
        pub fn scalar_k(&mut self, row: u8, payload: &[u8])
            -> aspis_core::field::QM31 {
            let out = crate::sampler::qm31_sample(&self.block(row, payload));
            crate::trace::value(4, row as usize, E::from_qm31(out));
            out
        }
        pub fn queries(&mut self, row: u8, payload: &[u8])
            -> Result<[u32; 22], crate::verifier::Error> {
            self.absorb(row, payload);
            let mut blocks = [[0; 32]; 8];
            let mut advances = blocks;
            let mut state = self.state;
            blocks[0] = self.hash.digest(&[&state, &[1]]);
            advances[0] = self.hash.digest(&[&state, &[2]]);
            state = advances[0];
            blocks[1] = self.hash.digest(&[&state, &[1]]);
            advances[1] = self.hash.digest(&[&state, &[2]]);
            state = advances[1];
            blocks[2] = self.hash.digest(&[&state, &[1]]);
            advances[2] = self.hash.digest(&[&state, &[2]]);
            state = advances[2];
            blocks[3] = self.hash.digest(&[&state, &[1]]);
            advances[3] = self.hash.digest(&[&state, &[2]]);
            state = advances[3];
            blocks[4] = self.hash.digest(&[&state, &[1]]);
            advances[4] = self.hash.digest(&[&state, &[2]]);
            state = advances[4];
            blocks[5] = self.hash.digest(&[&state, &[1]]);
            advances[5] = self.hash.digest(&[&state, &[2]]);
            state = advances[5];
            blocks[6] = self.hash.digest(&[&state, &[1]]);
            advances[6] = self.hash.digest(&[&state, &[2]]);
            state = advances[6];
            blocks[7] = self.hash.digest(&[&state, &[1]]);
            advances[7] = self.hash.digest(&[&state, &[2]]);
            state = advances[7];
            let (q, state) = queries_from_pairs(&blocks, &advances)?;
            self.state = state;
            trace_queries(&q);
            Ok(q)
        }
    }
    fn trace_queries(q: &[u32; 22]) {
        let mut i = 0;
        while i < 22 {
            crate::trace::value(5, i,
                E::from_m31(aspis_core::field::M31(q[i])));
            i += 1;
        }
    }
    /// Preserve scanOut's pre-word stop check, including the extra selected block
    /// when the 22nd distinct query is the final word of a block. All eight pairs
    /// have already been read by the caller, just as in the v2 transcript.
    fn queries_from_pairs(blocks: &[[u8; 32]; 8], advances: &[[u8; 32]; 8])
        -> Result<([u32; 22], [u8; 32]), crate::verifier::Error> {
        scan_query_words(blocks, advances, [0; 22], 0, 0)
    }
    fn scan_query_words(blocks: &[[u8; 32]; 8], advances: &[[u8; 32]; 8],
        mut accepted: [u32; 22], n: usize, draws: usize)
        -> Result<([u32; 22], [u8; 32]), crate::verifier::Error> {
        if draws == 64 {
            return if n == 22 {
                    Ok((accepted, advances[7]))
                } else { Err(crate::verifier::Error::Transcript) };
        }
        let k = draws / 8;
        if n == 22 { return Ok((accepted, advances[k])); }
        let at = 4 * (draws % 8);
        let candidate =
            u32::from_le_bytes([blocks[k][at], blocks[k][at + 1],
                            blocks[k][at + 2], blocks[k][at + 3]]) & 0x3ffff;
        if query_contains(&accepted, n, candidate) {
            scan_query_words(blocks, advances, accepted, n, draws + 1)
        } else {
            accepted[n] = candidate;
            scan_query_words(blocks, advances, accepted, n + 1, draws + 1)
        }
    }
    fn query_contains(accepted: &[u32; 22], n: usize, candidate: u32)
        -> bool {
        let mut i = 0;
        while i < n { if accepted[i] == candidate { return true; } i += 1; }
        false
    }
}
mod host_wire {
    //! Host semantic transcript and record owner. Verifier wire remains frozen.
    use alloc::vec::Vec;
    use aspis_core::{
        Digest32, circle::SecureCirclePoint, field::{WideExact, QM31},
    };
    use crate::sampler::{circle_sample, qm31_sample, CircleRow};
    pub use crate::r1_wire::{
        Error, Challenges, DOMAIN, row_shape, statement_points,
    };
    fn validate_record_fields(row: u8, payload: &[u8]) -> Result<(), Error> {
        let mut value = 0;
        while value < payload.len() / 32 {
            let start = 32 * value;
            let x =
                WideExact::from_le_bytes(&payload[start..start +
                                            32]).ok_or(Error::NonCanonical { row, value })?;
            if x.c1() != QM31::ZERO {
                return Err(Error::NonCanonical { row, value });
            }
            value += 1;
        }
        Ok(())
    }
    pub fn parse_record(row: u8, record: &[u8]) -> Result<&[u8], Error> {
        let (tag, size) = row_shape(row).ok_or(Error::InvalidRow)?;
        if record.len() != 5 + size { return Err(Error::Length { row }); }
        if record[0] != tag { return Err(Error::Tag { row }); }
        if u32::from_le_bytes([record[1], record[2], record[3], record[4]]) as
                    usize != size {
            return Err(Error::Length { row });
        }
        let payload = &record[5..];
        if row >= 14 { validate_record_fields(row, payload)?; }
        Ok(payload)
    }
    pub fn record(row: u8, payload: &[u8]) -> Result<Vec<u8>, Error> {
        let (tag, size) = row_shape(row).ok_or(Error::InvalidRow)?;
        if payload.len() != size { return Err(Error::Length { row }); }
        let mut out = Vec::with_capacity(5 + size);
        out.push(tag);
        out.extend_from_slice(&(size as u32).to_le_bytes());
        out.extend_from_slice(payload);
        parse_record(row, &out)?;
        Ok(out)
    }
    pub struct SemanticTranscript<H: Digest32> {
        state: [u8; 32],
        hash: H,
        next_row: u8,
    }
    #[automatically_derived]
    impl<H: ::core::clone::Clone + Digest32> ::core::clone::Clone for
        SemanticTranscript<H> {
        #[inline]
        fn clone(&self) -> SemanticTranscript<H> {
            SemanticTranscript {
                state: ::core::clone::Clone::clone(&self.state),
                hash: ::core::clone::Clone::clone(&self.hash),
                next_row: ::core::clone::Clone::clone(&self.next_row),
            }
        }
    }
    impl<H: Digest32> SemanticTranscript<H> {
        pub fn new(hash: H, public_bytes: &[u8], c1_root: &[u8; 32])
            -> Result<Self, Error> {
            let length =
                u32::try_from(public_bytes.len()).map_err(|_| Error::Public)?;
            Ok(Self {
                    state: hash.digest(&[DOMAIN, &[0], &length.to_le_bytes(),
                                    public_bytes, c1_root]),
                    hash,
                    next_row: 0,
                })
        }
        pub fn state(&self) -> [u8; 32] { self.state }
        pub fn next_row(&self) -> u8 { self.next_row }
        fn sample_block_validated(&mut self, row: u8, framed: &[u8])
            -> Result<[u8; 32], Error> {
            if row != self.next_row {
                return Err(Error::RowOrder {
                            expected: self.next_row,
                            actual: row,
                        });
            }
            let absorbed =
                self.hash.digest(&[&self.state, &[0, 0xa0 + row], framed]);
            let block = self.hash.digest(&[&absorbed, &[1]]);
            self.state = self.hash.digest(&[&absorbed, &[2]]);
            self.next_row += 1;
            Ok(block)
        }
        fn sample_block(&mut self, row: u8, framed: &[u8])
            -> Result<[u8; 32], Error> {
            if row != self.next_row {
                return Err(Error::RowOrder {
                            expected: self.next_row,
                            actual: row,
                        });
            }
            parse_record(row, framed)?;
            self.sample_block_validated(row, framed)
        }
        pub fn semantic(&mut self, row: u8, framed: &[u8])
            -> Result<QM31, Error> {
            if row > 24 { return Err(Error::InvalidRow); }
            Ok(qm31_sample(&self.sample_block(row, framed)?))
        }
        /// R-B's one-block reference-circle map, including fixed fallback.
        /// The legacy Transcript method has a different parameter sampler.
        pub fn challenge_reference_circle_point(&mut self, row: u8,
            framed: &[u8]) -> Result<SecureCirclePoint, Error> {
            let circle_row =
                match row {
                    25 => CircleRow::First,
                    26 => CircleRow::Second,
                    _ => return Err(Error::InvalidRow),
                };
            Ok(circle_sample(&self.sample_block(row, framed)?, circle_row))
        }
    }
}
mod host_compact {
    //! Host compact publication owner; shared verifier codec remains frozen.
    use alloc::vec::Vec;
    use crate::r1_wire::row_shape;
    pub use crate::compact::*;
    fn compact_row(row: u8) -> bool { row >= 14 }
    pub fn compact_semantic(logical: &[u8], out: &mut Vec<u8>)
        -> Result<(), CodecError> {
        if logical.len() != LOGICAL_SEMANTIC {
            return Err(CodecError::Length);
        }
        out.extend_from_slice(&logical[..32]);
        let count = SEMANTIC_ROWS;
        let mut at = 32;
        let mut row = 0;
        while row < count {
            at = compact_semantic_row(logical, out, row, at)?;
            row += 1;
        }
        if at != logical.len() { return Err(CodecError::Length); }
        Ok(())
    }
    fn compact_semantic_row(logical: &[u8], out: &mut Vec<u8>, row: u8,
        at: usize) -> Result<usize, CodecError> {
        let size = row_shape(row).ok_or(CodecError::Length)?.1;
        out.extend_from_slice(&logical[at..at + 5]);
        let at = at + 5;
        if compact_row(row) {
            compact_values(&logical[at..at + size], out)?;
        } else { out.extend_from_slice(&logical[at..at + size]); }
        Ok(at + size)
    }
    pub fn compact_values(logical: &[u8], out: &mut Vec<u8>)
        -> Result<(), CodecError> {
        if logical.len() % 32 != 0 { return Err(CodecError::Length); }
        let mut at = 0;
        while at < logical.len() {
            let mut high = 16;
            while high < 32 {
                if logical[at + high] != 0 {
                    return Err(CodecError::NonZeroHigh);
                }
                high += 1;
            }
            out.extend_from_slice(&logical[at..at + 16]);
            at += 32;
        }
        Ok(())
    }
}
pub mod multiproof {
    //! ADOPTED R1 PROOF FORMAT (PREREG-PROOF-SIZE-2, 2026-10-19); UNPROVED.
    //!
    //! Indexed Merkle multiproofs over the fixed 2^18-leaf commitment domain.
    //! `Arity::Eight` is the shipped tree shape (six levels of eight, node grammar
    //! `0x18 || c0..c7`); `Arity::Two` is the candidate binary tree (eighteen
    //! levels, node grammar `BINARY_NODE_TAG || left || right`). Leaf hashing is
    //! unchanged and supplied by the caller.
    //!
    //! Multiproof order: level by level from the leaves; inside a level, occupied
    //! nodes in ascending index order; inside one parent's group, the children
    //! that are not occupied, in ascending slot order. The number of supplied
    //! nodes is a function of the index set only (`node_count`), so a parser
    //! knows the exact length before reading a node.
    use alloc::vec::Vec;
    use aspis_core::{r0::merkle, Digest32};
    /// Leaves in every committed tree (C1, C2 and the padded folded tree).
    pub const LEAF_BITS: u32 = 18;
    /// New domain separator for binary parent nodes (leaves use 0x10, eight-way
    /// parents 0x18). UNPROVED: its disjointness is one of the obligations.
    pub const BINARY_NODE_TAG: u8 = 0x12;
    /// Largest index set one multiproof call accepts (one transaction batch).
    pub const MAX_BATCH: usize = 16;
    pub enum Arity { Two, Eight, }
    #[automatically_derived]
    #[doc(hidden)]
    unsafe impl ::core::clone::TrivialClone for Arity { }
    #[automatically_derived]
    impl ::core::clone::Clone for Arity {
        #[inline]
        fn clone(&self) -> Arity { *self }
    }
    #[automatically_derived]
    impl ::core::marker::Copy for Arity { }
    #[automatically_derived]
    impl ::core::fmt::Debug for Arity {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            ::core::fmt::Formatter::write_str(f,
                match self { Arity::Two => "Two", Arity::Eight => "Eight", })
        }
    }
    #[automatically_derived]
    impl ::core::marker::StructuralPartialEq for Arity { }
    #[automatically_derived]
    impl ::core::cmp::PartialEq for Arity {
        #[inline]
        fn eq(&self, other: &Arity) -> bool {
            let __self_discr = ::core::intrinsics::discriminant_value(self);
            let __arg1_discr = ::core::intrinsics::discriminant_value(other);
            __self_discr == __arg1_discr
        }
    }
    #[automatically_derived]
    impl ::core::cmp::Eq for Arity {
        #[inline]
        #[doc(hidden)]
        #[coverage(off)]
        fn assert_fields_are_eq(&self) {}
    }
    impl Arity {
        #[inline(always)]
        pub const fn bits(self) -> u32 {
            match self { Self::Two => 1, Self::Eight => 3, }
        }
        #[inline(always)]
        pub const fn width(self) -> usize { 1 << self.bits() }
        #[inline(always)]
        pub const fn levels(self) -> u32 { LEAF_BITS / self.bits() }
    }
    #[inline(always)]
    pub fn binary_parent<H: Digest32>(hash: H, left: &[u8; 32],
        right: &[u8; 32]) -> [u8; 32] {
        hash.digest(&[&[BINARY_NODE_TAG], left, right])
    }
    /// Strictly increasing and inside the leaf domain.
    fn well_formed(indices: &[u32]) -> bool {
        !indices.is_empty() && indices.len() <= MAX_BATCH &&
                indices.windows(2).all(|w| w[0] < w[1]) &&
            indices.iter().all(|&i| i < 1 << LEAF_BITS)
    }
    #[inline(always)]
    fn index_at(indices: &[u32; MAX_BATCH], index: usize) -> u32 {
        indices[index]
    }
    #[inline(always)]
    fn value_at(values: &[[u8; 32]; MAX_BATCH], index: usize) -> [u8; 32] {
        values[index]
    }
    #[inline(always)]
    fn root_matches(values: &[[u8; 32]; MAX_BATCH], root: &[u8; 32]) -> bool {
        values[0] == *root
    }
    #[inline(always)]
    fn occupied_binary_parent<H: Digest32>(hash: H,
        values: &[[u8; 32]; MAX_BATCH], index: usize) -> [u8; 32] {
        hash.digest(&[&[BINARY_NODE_TAG], &values[index], &values[index + 1]])
    }
    #[inline(always)]
    fn sibling_binary_parent<H: Digest32>(hash: H,
        values: &[[u8; 32]; MAX_BATCH], index: usize, sibling: &[u8],
        left: bool) -> [u8; 32] {
        if left {
            hash.digest(&[&[BINARY_NODE_TAG], &values[index], sibling])
        } else { hash.digest(&[&[BINARY_NODE_TAG], sibling, &values[index]]) }
    }
    /// Number of supplied sibling nodes for a strictly increasing index set:
    /// at each level, (width x distinct parents) - occupied nodes.
    pub fn node_count(arity: Arity, indices: &[u32]) -> Option<usize> {
        if !well_formed(indices) { return None; }
        let mut level = [0u32; MAX_BATCH];
        level[..indices.len()].copy_from_slice(indices);
        let mut n = indices.len();
        let mut count = 0;
        for _ in 0..arity.levels() {
            let mut w = 0;
            let mut i = 0;
            while i < n {
                let parent = index_at(&level, i) >> arity.bits();
                let mut j = i;
                while j < n && index_at(&level, j) >> arity.bits() == parent {
                    j += 1;
                }
                count += arity.width() - (j - i);
                level[w] = parent;
                w += 1;
                i = j;
            }
            n = w;
        }
        Some(count)
    }
    /// Verify one multiproof. `indices` strictly increasing, `leaves[i]` the leaf
    /// hash at `indices[i]`, `nodes` exactly `32 * node_count` bytes, consumed in
    /// the canonical order. Rejects on any malformed input; never panics.
    pub fn verify<H: Digest32>(hash: H, arity: Arity, root: &[u8; 32],
        indices: &[u32], leaves: &[[u8; 32]], nodes: &[u8]) -> bool {
        if !well_formed(indices) || leaves.len() != indices.len() ||
                nodes.len() % 32 != 0 {
            return false;
        }
        let mut idx = [0u32; MAX_BATCH];
        let mut val = [[0u8; 32]; MAX_BATCH];
        let n = indices.len();
        idx[..n].copy_from_slice(indices);
        val[..n].copy_from_slice(leaves);
        verify_in_place(hash, arity, root, &mut idx, &mut val, n, nodes)
    }
    /// `verify` over caller-owned scratch arrays (no copies): the first `n`
    /// entries of `idx`/`val` are the strictly increasing indices and their
    /// leaves; both arrays are overwritten.
    #[inline(always)]
    pub fn verify_in_place<H: Digest32>(hash: H, arity: Arity,
        root: &[u8; 32], idx: &mut [u32; MAX_BATCH],
        val: &mut [[u8; 32]; MAX_BATCH], mut n: usize, nodes: &[u8]) -> bool {
        if n == 0 || n > MAX_BATCH || !well_formed(&idx[..n]) ||
                nodes.len() % 32 != 0 {
            return false;
        }
        let mut at = 0usize;
        for _ in 0..arity.levels() {
            let mut w = 0;
            let mut i = 0;
            while i < n {
                let parent = index_at(idx, i) >> arity.bits();
                let digest =
                    match arity {
                        Arity::Two => {
                            if i + 1 < n && index_at(idx, i + 1) == index_at(idx, i) ^ 1
                                {
                                let d = occupied_binary_parent(hash, val, i);
                                i += 2;
                                d
                            } else {
                                let Some(sibling) =
                                    nodes.get(at..at + 32) else { return false };
                                at += 32;
                                let d =
                                    sibling_binary_parent(hash, val, i, sibling,
                                        index_at(idx, i) & 1 == 0);
                                i += 1;
                                d
                            }
                        }
                        Arity::Eight => {
                            let mut children = [[0u8; 32]; 8];
                            for (slot, child) in children.iter_mut().enumerate() {
                                if i < n && index_at(idx, i) >> 3 == parent &&
                                        (index_at(idx, i) & 7) as usize == slot {
                                    *child = value_at(val, i);
                                    i += 1;
                                } else {
                                    let Some(sibling) =
                                        nodes.get(at..at + 32) else { return false };
                                    child.copy_from_slice(sibling);
                                    at += 32;
                                }
                            }
                            merkle::parent_with_digest(hash, &children)
                        }
                    };
                idx[w] = parent;
                val[w] = digest;
                w += 1;
            }
            n = w;
        }
        n == 1 && index_at(idx, 0) == 0 && root_matches(val, root) &&
            at == nodes.len()
    }
    /// Prover side: emit the canonical node sequence. `node(level, index)` returns
    /// the stored digest of node `index` at `level` (0 = leaves).
    pub fn generate(arity: Arity, indices: &[u32],
        mut node: impl FnMut(u32, u32) -> [u8; 32]) -> Option<Vec<u8>> {
        let count = node_count(arity, indices)?;
        let mut out = Vec::with_capacity(32 * count);
        let mut level: Vec<u32> = indices.to_vec();
        for depth in 0..arity.levels() {
            let mut next = Vec::new();
            let mut i = 0;
            while i < level.len() {
                let parent = level[i] >> arity.bits();
                for slot in 0..arity.width() as u32 {
                    let child = (parent << arity.bits()) | slot;
                    if i < level.len() && level[i] == child {
                        i += 1;
                    } else { out.extend_from_slice(&node(depth, child)); }
                }
                next.push(parent);
            }
            level = next;
        }
        (out.len() == 32 * count).then_some(out)
    }
    /// Host-side complete binary tree over 2^18 leaves.
    pub struct BinaryTree {
        levels: Vec<Vec<[u8; 32]>>,
    }
    impl BinaryTree {
        pub fn new<H: Digest32>(hash: H, leaves: Vec<[u8; 32]>)
            -> Option<Self> {
            if leaves.len() != 1 << LEAF_BITS { return None; }
            let mut levels = Vec::with_capacity(LEAF_BITS as usize + 1);
            levels.push(leaves);
            for depth in 0..LEAF_BITS as usize {
                let next =
                    levels[depth].chunks_exact(2).map(|c|
                                binary_parent(hash, &c[0], &c[1])).collect();
                levels.push(next);
            }
            Some(Self { levels })
        }
        pub fn root(&self) -> [u8; 32] { self.levels[LEAF_BITS as usize][0] }
        pub fn node(&self, level: u32, index: u32) -> [u8; 32] {
            self.levels[level as usize][index as usize]
        }
        pub fn multiproof(&self, indices: &[u32]) -> Option<Vec<u8>> {
            generate(Arity::Two, indices, |l, i| self.node(l, i))
        }
    }
    /// Sort a batch of (index, leaf) pairs, merge equal indices whose leaves are
    /// identical (the folded tree's shared openings), reject equal indices with
    /// different leaves. Returns the number of distinct entries.
    pub fn sort_dedup(idx: &mut [u32], val: &mut [[u8; 32]])
        -> Option<usize> {
        let n = idx.len();
        if n != val.len() || n == 0 || n > MAX_BATCH { return None; }
        for i in 1..n {
            let mut j = i;
            while j > 0 && idx[j - 1] > idx[j] {
                idx.swap(j - 1, j);
                val.swap(j - 1, j);
                j -= 1;
            }
        }
        let mut w = 1;
        for i in 1..n {
            if idx[i] == idx[w - 1] {
                if val[i] != val[w - 1] { return None; }
            } else { idx[w] = idx[i]; val[w] = val[i]; w += 1; }
        }
        Some(w)
    }
}
pub mod compact {
    //! ADOPTED R1 PROOF FORMAT (PREREG-PROOF-SIZE-2, 2026-10-19; prototype from
    //! the proof-size feasibility test). UNPROVED: PROOF-SIZE-OBLIGATIONS.
    //!
    //! Compact QM31 storage for the 455 proof values that the shipped format
    //! stores as 32-byte WideExact with the high QM31 half required to be zero:
    //! every value of semantic rows 14..26 (426) and the 29 `y1` values. They are
    //! stored as their 16-byte canonical QM31 encoding; `expand_*` rebuilds the
    //! logical 32-byte form (zero high half) before any hashing, so every
    //! Fiat-Shamir message and record keeps its shipped byte definition.
    //!
    //! Stored layout (`MAGIC`, variant S2 only):
    //! header 16 | compact semantic 7,015 | compact y1 464 | inactive 32 |
    //! round0 224 | folded root 32 | round1 224 | final 2,048 |
    //! 22 openings x 832 (C1 values 480, C2 values 128, C1 salt, C2 salt,
    //! folded values 128, folded salt) | six fixed node slots, batch A then
    //! batch B, each batch C1, C2, folded (`SLOT_NODES`). Batch A = queries
    //! 0..SPLIT, batch B = SPLIT..22. Fixed length (lead ruling 2026-10-19): each
    //! slot holds its multiproof's nodes followed by zero bytes up to the slot's
    //! worst-case node count; the padding must be zero and is hashed with the
    //! rest of the stored bytes.
    use crate::r1_wire::row_shape;
    use alloc::vec::Vec;
    use aspis_core::field::QM31;
    pub const MAGIC: &[u8; 8] = b"R1P3CB18";
    pub const HEADER: usize = 16;
    pub const SPLIT: usize = 10;
    pub const QUERIES: usize = 22;
    pub const SEMANTIC_ROWS: u8 = 27;
    /// Logical (shipped) semantic bytes: root 32 + 27 framed records.
    pub const LOGICAL_SEMANTIC: usize = crate::verifier::SEMANTIC_BYTES;
    /// Values with an implied zero high half: rows 14..=26.
    pub const SEMANTIC_COMPACT_VALUES: usize = 1 + 10 * 28 + (87 + 29) + 29;
    pub const COMPACT_SEMANTIC: usize =
        LOGICAL_SEMANTIC - 16 * SEMANTIC_COMPACT_VALUES;
    pub const COMPACT_Y1: usize = 29 * 16;
    pub const LOGICAL_Y1: usize = 29 * 32;
    pub const OPENING: usize = 480 + 128 + 32 + 32 + 128 + 32;
    pub const OFF_SEMANTIC: usize = HEADER;
    pub const OFF_Y1: usize = OFF_SEMANTIC + COMPACT_SEMANTIC;
    pub const OFF_INACTIVE: usize = OFF_Y1 + COMPACT_Y1;
    pub const OFF_ROUND0: usize = OFF_INACTIVE + 32;
    pub const OFF_FOLDED_ROOT: usize = OFF_ROUND0 + 224;
    pub const OFF_ROUND1: usize = OFF_FOLDED_ROOT + 32;
    pub const OFF_FINAL: usize = OFF_ROUND1 + 224;
    pub const FINAL_LEN: usize = 64;
    pub const OFF_OPENINGS: usize = OFF_FINAL + FINAL_LEN * 32;
    pub const OFF_NODES: usize = OFF_OPENINGS + QUERIES * OPENING;
    /// Bytes before the multiproof nodes (28,359).
    pub const FIXED: usize = OFF_NODES;
    /// Worst-case supplied nodes over all query sets (S1 counting bound).
    pub const MAX_NODES: usize = 2 * (146 + 172) + (128 + 150);
    pub const MAX_PROOF: usize = FIXED + 32 * MAX_NODES;
    /// Worst-case node counts per slot: [C1 A, C2 A, folded A, C1 B, C2 B, folded B].
    pub const SLOT_NODES: [usize; 6] = [146, 146, 128, 172, 172, 150];
    /// Byte offset of each slot inside the stored proof.
    pub const fn slot_offset(slot: usize) -> usize {
        let mut at = OFF_NODES;
        let mut i = 0;
        while i < slot { at += 32 * SLOT_NODES[i]; i += 1; }
        at
    }
    /// The candidate's one stored length.
    pub const PROOF_BYTES: usize = MAX_PROOF;
    const _: () =
        if !(slot_offset(6) == MAX_PROOF) {
            ::core::panicking::panic("assertion failed: slot_offset(6) == MAX_PROOF")
        };
    const _: () =
        if !(SEMANTIC_COMPACT_VALUES == 426 && COMPACT_SEMANTIC == 7015) {
            ::core::panicking::panic("assertion failed: SEMANTIC_COMPACT_VALUES == 426 && COMPACT_SEMANTIC == 7015")
        };
    const _: () =
        if !(FIXED == 28_359 && MAX_PROOF == 57_607) {
            ::core::panicking::panic("assertion failed: FIXED == 28_359 && MAX_PROOF == 57_607")
        };
    pub enum CodecError { Length, NonZeroHigh, NonCanonical, }
    #[automatically_derived]
    #[doc(hidden)]
    unsafe impl ::core::clone::TrivialClone for CodecError { }
    #[automatically_derived]
    impl ::core::clone::Clone for CodecError {
        #[inline]
        fn clone(&self) -> CodecError { *self }
    }
    #[automatically_derived]
    impl ::core::marker::Copy for CodecError { }
    #[automatically_derived]
    impl ::core::fmt::Debug for CodecError {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            ::core::fmt::Formatter::write_str(f,
                match self {
                    CodecError::Length => "Length",
                    CodecError::NonZeroHigh => "NonZeroHigh",
                    CodecError::NonCanonical => "NonCanonical",
                })
        }
    }
    #[automatically_derived]
    impl ::core::marker::StructuralPartialEq for CodecError { }
    #[automatically_derived]
    impl ::core::cmp::PartialEq for CodecError {
        #[inline]
        fn eq(&self, other: &CodecError) -> bool {
            let __self_discr = ::core::intrinsics::discriminant_value(self);
            let __arg1_discr = ::core::intrinsics::discriminant_value(other);
            __self_discr == __arg1_discr
        }
    }
    #[automatically_derived]
    impl ::core::cmp::Eq for CodecError {
        #[inline]
        #[doc(hidden)]
        #[coverage(off)]
        fn assert_fields_are_eq(&self) {}
    }
    /// Is a semantic row's payload made of implied-zero-high values?
    #[inline(always)]
    fn compact_row(row: u8) -> bool { row >= 14 }
    /// Encoder (prover side): logical semantic bytes -> compact. Refuses any
    /// value whose high half is not zero (such a value has no compact form).
    pub fn compact_semantic(logical: &[u8], out: &mut Vec<u8>)
        -> Result<(), CodecError> {
        if logical.len() != LOGICAL_SEMANTIC {
            return Err(CodecError::Length);
        }
        out.extend_from_slice(&logical[..32]);
        let mut at = 32;
        for row in 0..SEMANTIC_ROWS {
            let size = row_shape(row).ok_or(CodecError::Length)?.1;
            out.extend_from_slice(&logical[at..at + 5]);
            at += 5;
            if compact_row(row) {
                compact_values(&logical[at..at + size], out)?;
            } else { out.extend_from_slice(&logical[at..at + size]); }
            at += size;
        }
        if at != logical.len() { return Err(CodecError::Length); }
        Ok(())
    }
    pub fn compact_values(logical: &[u8], out: &mut Vec<u8>)
        -> Result<(), CodecError> {
        if logical.len() % 32 != 0 { return Err(CodecError::Length); }
        for v in logical.chunks_exact(32) {
            if v[16..].iter().any(|&b| b != 0) {
                return Err(CodecError::NonZeroHigh);
            }
            out.extend_from_slice(&v[..16]);
        }
        Ok(())
    }
    /// Decoder (verifier side): compact values -> logical 32-byte values with a
    /// zero high half. Canonicality is not checked here: the verifier checks the
    /// stored `y1` values in its strict scan and the rebuilt semantic records in
    /// the shipped `Prefix::parse` (one check per value, as in the shipped path).
    #[inline(always)]
    pub fn expand_values(compact: &[u8], out: &mut [u8])
        -> Result<(), CodecError> {
        if compact.len() % 16 != 0 || out.len() != 2 * compact.len() {
            return Err(CodecError::Length);
        }
        for (c, o) in compact.chunks_exact(16).zip(out.chunks_exact_mut(32)) {
            o[..16].copy_from_slice(c);
            o[16..].fill(0);
        }
        Ok(())
    }
    /// Every stored compact value is a canonical QM31.
    pub fn check_values(compact: &[u8]) -> Result<(), CodecError> {
        for c in compact.chunks_exact(16) {
            QM31::from_le_bytes(c).ok_or(CodecError::NonCanonical)?;
        }
        Ok(())
    }
    /// Decoder: compact semantic -> logical semantic (framing bytes copied;
    /// the shipped `Prefix::parse` then checks tag, length and every limb).
    pub fn expand_semantic(compact: &[u8], out: &mut [u8])
        -> Result<(), CodecError> {
        if compact.len() != COMPACT_SEMANTIC || out.len() != LOGICAL_SEMANTIC
            {
            return Err(CodecError::Length);
        }
        out[..32].copy_from_slice(&compact[..32]);
        let (mut src, mut dst) = (32, 32);
        for row in 0..SEMANTIC_ROWS {
            let size = row_shape(row).ok_or(CodecError::Length)?.1;
            out[dst..dst + 5].copy_from_slice(&compact[src..src + 5]);
            src += 5;
            dst += 5;
            if compact_row(row) {
                expand_values(&compact[src..src + size / 2],
                        &mut out[dst..dst + size])?;
                src += size / 2;
            } else {
                out[dst..dst +
                                size].copy_from_slice(&compact[src..src + size]);
                src += size;
            }
            dst += size;
        }
        if src != compact.len() || dst != out.len() {
            return Err(CodecError::Length);
        }
        Ok(())
    }
}
mod ct_pole {
    //! Secret-operand pole comparisons. Shape and masks are public registry data.
    use aspis_core::field::QM31;
    #[inline(always)]
    pub(crate) fn equal(a: QM31, b: QM31) -> bool {
        let different =
            (a.c0.a.0 ^ b.c0.a.0) | (a.c0.b.0 ^ b.c0.b.0) |
                    (a.c1.a.0 ^ b.c1.a.0) | (a.c1.b.0 ^ b.c1.b.0);
        different == 0
    }
    #[inline(always)]
    pub(crate) fn keep_clear(clear: bool, active: bool, chi: QM31,
        value: QM31) -> bool {
        clear & !(active & equal(chi, value))
    }
    pub(crate) fn all_slots_clear(values: &[[[QM31; 2]; 2]],
        masks: &[u16; 64], chi: QM31) -> bool {
        let mut clear = true;
        let mut row = 0usize;
        while row < values.len() {
            let active = masks[row >> 4] & (1 << (row & 15)) != 0;
            let mut side = 0usize;
            while side < 2 {
                let mut slot = 0usize;
                while slot < 2 {
                    clear =
                        keep_clear(clear, active, chi, values[row][side][slot]);
                    slot += 1;
                }
                side += 1;
            }
            row += 1;
        }
        clear
    }
}
pub mod host_work {
    //! Fixed public work ranges; no operand-dependent work stealing or cancellation.
    use alloc::vec::Vec;
    #[path =
    "../../../docs/research/v8-r0-zk-20261009/c3/check/src/native_workers.rs"]
    mod pool {
        //! Bounded host work on independent public inputs; source-order merge.
        extern crate std;
        use alloc::vec::Vec;
        use core::cell::Cell;
        const ACTIVE: ::std::thread::LocalKey<Cell<bool>> =
            {
                const __RUST_STD_INTERNAL_INIT: Cell<bool> =
                    { Cell::new(false) };
                unsafe {
                    ::std::thread::LocalKey::new(const {
                                if ::std::mem::needs_drop::<Cell<bool>>() {
                                    |_|
                                        {
                                            #[thread_local]
                                            static __RUST_STD_INTERNAL_VAL:
                                                ::std::thread::local_impl::EagerStorage<Cell<bool>> =
                                                ::std::thread::local_impl::EagerStorage::new(__RUST_STD_INTERNAL_INIT);
                                            __RUST_STD_INTERNAL_VAL.get()
                                        }
                                } else {
                                    |_|
                                        {
                                            #[thread_local]
                                            static __RUST_STD_INTERNAL_VAL: Cell<bool> =
                                                __RUST_STD_INTERNAL_INIT;
                                            &__RUST_STD_INTERNAL_VAL
                                        }
                                }
                            })
                }
            };
        pub const THREADS: usize = 16;
        /// Partition [0,n) into 16 adjacent ranges, in increasing source order.
        pub fn range(n: usize, k: usize) -> (usize, usize) {
            if !(k < THREADS) {
                ::core::panicking::panic("assertion failed: k < THREADS")
            };
            let q = n / THREADS;
            let r = n % THREADS;
            let start = q * k + core::cmp::min(k, r);
            (start, start + q + (k < r) as usize)
        }
        pub fn is_worker() -> bool { ACTIVE.with(Cell::get) }
        struct Active(bool);
        impl Active {
            fn enter() -> Self { Self(ACTIVE.with(|a| a.replace(true))) }
        }
        impl Drop for Active {
            fn drop(&mut self) { ACTIVE.with(|a| a.set(self.0)); }
        }
        /// No nested teams; at most 15 spawned workers plus this calling thread.
        /// Each range catches its panic, all handles are joined, then the first
        /// source-order panic is resumed for the enclosing panic-to-reject boundary.
        pub fn ordered_map<T: Send, F: Fn(usize) -> T + Sync>(n: usize, f: F)
            -> Vec<T> {
            ordered_map_inner(n, f, false)
        }
        pub fn ordered_families<T: Send, F: Fn(usize) -> T +
            Sync>(n: usize, f: F) -> Vec<T> {
            ordered_map_inner(n, f, true)
        }
        fn ordered_map_inner<T: Send, F: Fn(usize) -> T +
            Sync>(n: usize, f: F, force: bool) -> Vec<T> {
            if (n < THREADS * 2 && !force) || is_worker() {
                return (0..n).map(f).collect();
            }
            let _active = Active::enter();
            let run =
                |k|
                    {
                        let _active = Active::enter();
                        std::panic::catch_unwind(std::panic::AssertUnwindSafe(||
                                    {
                                        let (a, b) = range(n, k);
                                        (a..b).map(&f).collect::<Vec<T>>()
                                    }))
                    };
            let chunks =
                std::thread::scope(|scope|
                        {
                            let mut handles = Vec::new();
                            for k in 1..THREADS {
                                let run = &run;
                                handles.push(scope.spawn(move || run(k)));
                            }
                            let first = run(0);
                            let mut chunks = Vec::with_capacity(THREADS);
                            chunks.push(first);
                            for handle in handles {
                                chunks.push(match handle.join() {
                                        Ok(v) => v,
                                        Err(p) => Err(p),
                                    });
                            }
                            chunks
                        });
            let mut out = Vec::with_capacity(n);
            for chunk in chunks {
                match chunk {
                    Ok(mut v) => out.append(&mut v),
                    Err(p) => std::panic::resume_unwind(p),
                }
            }
            out
        }
    }
    pub(crate) fn map<T: Send, F: Fn(usize) -> T +
        Sync>(_stage: usize, n: usize, f: F) -> Vec<T> {
        let chunks =
            pool::ordered_families(pool::THREADS,
                |k|
                    {
                        let (a, b) = pool::range(n, k);
                        let mut out = Vec::with_capacity(b - a);
                        let mut completed = 0;
                        for i in a..b { out.push(f(i)); completed += 1; }
                        (out, completed)
                    });
        let mut out = Vec::with_capacity(n);
        for (k, (mut chunk, completed)) in chunks.into_iter().enumerate() {
            let _ = (k, completed);
            out.append(&mut chunk);
        }
        out
    }
}
mod prover_shared {
    //! Candidate host-prover-only extraction leaf. See design/PV-EXTRACT-20261027.md.
    use aspis_core::field::{CM31, M31, QM31};
    pub(crate) fn compress_tagged_tuple(tag: M31, values: &[M31],
        lambda: QM31) -> QM31 {
        let mut compressed = QM31::from_cm31(CM31::from_m31(tag));
        let mut power = lambda;
        let mut i = 0usize;
        while i < values.len() {
            compressed = compressed.add(power.mul_m31(values[i]));
            power = power.mul(lambda);
            i = i.wrapping_add(1);
        }
        compressed
    }
}
mod prover_helper_sum {
    use aspis_core::field::QM31;
    const TRACE_ROWS: usize = 1024;
    pub fn state_only_copy_helper_sum(h1: &[QM31]) -> Option<QM31> {
        if h1.len() == TRACE_ROWS {
            let mut sum = QM31::ZERO;
            let mut i = 0usize;
            while i < h1.len() { sum = sum.add(h1[i]); i += 1; }
            Some(sum)
        } else { None }
    }
}
mod prover_powers {
    //! Prover-local op254 copy; release weights::powers remains unchanged.
    use aspis_core::field::WideExact as E;
    pub fn powers<const N : usize>(x: E) -> [E; N] {
        let mut out = [E::ZERO; N];
        let mut p = E::ONE;
        let mut i = 0usize;
        while i < N { out[i] = p; i += 1; if i < N { p = p.mul(x); } }
        out
    }
}
mod host_sampler {
    //! Prover-local Drop-free samplers (D187 batch 2).
    use aspis_core::field::{WideExact, P};
    fn low_base_p_digits(block: &[u8; 32]) -> ([u32; 8], u32) {
        let mut quotient = [0u32; 8];
        let mut i = 0usize;
        while i < 8 {
            quotient[i] =
                (block[4 * i] as u32) | ((block[4 * i + 1] as u32) << 8u32) |
                        ((block[4 * i + 2] as u32) << 16u32) |
                    ((block[4 * i + 3] as u32) << 24u32);
            i += 1;
        }
        let mut digits = [0u32; 8];
        let mut d = 0usize;
        while d < 8 {
            let mut remainder = 0u64;
            let mut j = 8usize;
            while j > 0 {
                j -= 1;
                let dividend = (remainder << 32u32) | u64::from(quotient[j]);
                quotient[j] = (dividend / u64::from(P)) as u32;
                remainder = dividend % u64::from(P);
            }
            digits[d] = remainder as u32;
            d += 1;
        }
        let mut check = 1usize;
        while check < 8 {
            if false {
                if !(quotient[check] == 0) {
                    ::core::panicking::panic("assertion failed: quotient[check] == 0")
                };
            };
            check += 1;
        }
        if false {
            if !(quotient[0] <= 256) {
                ::core::panicking::panic("assertion failed: quotient[0] <= 256")
            };
        };
        (digits, quotient[0])
    }
    fn decode8(digits: [u32; 8]) -> WideExact {
        WideExact::from_limbs(digits).unwrap()
    }
    /// Add a small integer to a base-P digit vector. Returns the carry beyond
    /// the final digit, which is at most one for the values used by the sampler.
    fn add_small_base_p(digits: &mut [u32; 8], mut addend: u32) -> bool {
        let mut i = 0usize;
        while i < 8 {
            let sum = u64::from(digits[i]) + u64::from(addend);
            digits[i] = (sum % u64::from(P)) as u32;
            addend = (sum / u64::from(P)) as u32;
            i += 1;
        }
        if false {
            if !(addend <= 1) {
                ::core::panicking::panic("assertion failed: addend <= 1")
            };
        };
        addend != 0
    }
    /// `decode8(rank(block) mod P^8)`, byte-for-byte equivalent to the frozen
    /// R0 sampler. The repeated divisions directly produce the low eight digits.
    pub fn ordinary_sample(block: &[u8; 32]) -> WideExact {
        let (digits, _) = low_base_p_digits(block);
        decode8(digits)
    }
    /// `decode8((rank(block) mod (P^8 - 1)) + 1)`, byte-for-byte equivalent to
    /// the frozen R0 sampler. Since `P^8 ≡ 1 (mod P^8 - 1)`, the high quotient can
    /// be added to the low digits before the final increment. A carry past digit
    /// seven contributes one more modulo `P^8 - 1`.
    pub fn gamma_sample(block: &[u8; 32]) -> WideExact {
        let (mut digits, quotient) = low_base_p_digits(block);
        let wrapped = add_small_base_p(&mut digits, quotient + 1);
        if wrapped {
            let wrapped_again = add_small_base_p(&mut digits, 1);
            if false {
                if !!wrapped_again {
                    ::core::panicking::panic("assertion failed: !wrapped_again")
                };
            };
        }
        decode8(digits)
    }
}
mod host_weights {
    //! Prover-local fixed-storage weights (D187 batch 2).
    use aspis_core::field::{QM31, QM31 as K, WideExact as E};
    use aspis_core::circle::SecureCirclePoint;
    use crate::{transport::Variant, verifier::Error};
    pub use crate::weights::{QUARTER, PERM};
    pub struct Weights {
        pub variant: Variant,
        pub factors: [[[K; 4]; 5]; 5],
        pub points: [[K; 10]; 3],
        pub extra: [K; 2],
    }
    #[automatically_derived]
    #[doc(hidden)]
    unsafe impl ::core::clone::TrivialClone for Weights { }
    #[automatically_derived]
    impl ::core::clone::Clone for Weights {
        #[inline]
        fn clone(&self) -> Weights {
            let _: ::core::clone::AssertParamIsClone<Variant>;
            let _: ::core::clone::AssertParamIsClone<[[[K; 4]; 5]; 5]>;
            let _: ::core::clone::AssertParamIsClone<[[K; 10]; 3]>;
            let _: ::core::clone::AssertParamIsClone<[K; 2]>;
            *self
        }
    }
    #[automatically_derived]
    impl ::core::marker::Copy for Weights { }
    fn double(x: K) -> K { x.mul(x).add(x.mul(x)).sub(K::ONE) }
    fn state_only_statement_points(z: &[QM31; 10]) -> [[QM31; 10]; 3] {
        let mut successor = *z;
        let mut carry = QM31::ONE;
        let bit = z[9];
        let bit_and_carry = bit.mul(carry);
        successor[9] = bit.add(carry).sub(bit_and_carry.add(bit_and_carry));
        carry = bit_and_carry;
        let bit = z[8];
        let bit_and_carry = bit.mul(carry);
        successor[8] = bit.add(carry).sub(bit_and_carry.add(bit_and_carry));
        carry = bit_and_carry;
        let bit = z[7];
        let bit_and_carry = bit.mul(carry);
        successor[7] = bit.add(carry).sub(bit_and_carry.add(bit_and_carry));
        carry = bit_and_carry;
        let bit = z[6];
        let bit_and_carry = bit.mul(carry);
        successor[6] = bit.add(carry).sub(bit_and_carry.add(bit_and_carry));
        carry = bit_and_carry;
        let bit = z[5];
        let bit_and_carry = bit.mul(carry);
        successor[5] = bit.add(carry).sub(bit_and_carry.add(bit_and_carry));
        carry = bit_and_carry;
        let bit = z[4];
        let bit_and_carry = bit.mul(carry);
        successor[4] = bit.add(carry).sub(bit_and_carry.add(bit_and_carry));
        carry = bit_and_carry;
        let bit = z[3];
        let bit_and_carry = bit.mul(carry);
        successor[3] = bit.add(carry).sub(bit_and_carry.add(bit_and_carry));
        carry = bit_and_carry;
        let bit = z[2];
        let bit_and_carry = bit.mul(carry);
        successor[2] = bit.add(carry).sub(bit_and_carry.add(bit_and_carry));
        carry = bit_and_carry;
        let bit = z[1];
        let bit_and_carry = bit.mul(carry);
        successor[1] = bit.add(carry).sub(bit_and_carry.add(bit_and_carry));
        carry = bit_and_carry;
        let bit = z[0];
        let bit_and_carry = bit.mul(carry);
        successor[0] = bit.add(carry).sub(bit_and_carry.add(bit_and_carry));
        carry = bit_and_carry;
        let mut absorption = *z;
        absorption[7] = QM31::ONE.sub(absorption[7]);
        absorption[6] = QM31::ONE.sub(absorption[6]);
        [*z, successor, absorption]
    }
    impl Weights {
        #[inline(never)]
        pub fn new(variant: Variant, alpha: &[K; 10],
            z: &[SecureCirclePoint; 2]) -> Result<Weights, Error> {
            let points = state_only_statement_points(alpha);
            let extra = [alpha[8], alpha[9]];
            let mut factors = [[[K::ZERO; 4]; 5]; 5];
            let a = points[0][3];
            let b = points[0][2];
            factors[0][0] =
                [K::ONE.sub(a).mul(K::ONE.sub(b)), a.mul(K::ONE.sub(b)),
                        K::ONE.sub(a).mul(b), a.mul(b)];
            let a = points[0][1];
            let b = points[0][0];
            factors[0][1] =
                [K::ONE.sub(a).mul(K::ONE.sub(b)), a.mul(K::ONE.sub(b)),
                        K::ONE.sub(a).mul(b), a.mul(b)];
            let a = points[0][5];
            let b = points[0][4];
            factors[0][2] =
                [K::ONE.sub(a).mul(K::ONE.sub(b)), a.mul(K::ONE.sub(b)),
                        K::ONE.sub(a).mul(b), a.mul(b)];
            let a = points[0][9];
            let b = points[0][8];
            factors[0][3] =
                [K::ONE.sub(a).mul(K::ONE.sub(b)), a.mul(K::ONE.sub(b)),
                        K::ONE.sub(a).mul(b), a.mul(b)];
            let a = points[0][7];
            let b = points[0][6];
            factors[0][4] =
                [K::ONE.sub(a).mul(K::ONE.sub(b)), a.mul(K::ONE.sub(b)),
                        K::ONE.sub(a).mul(b), a.mul(b)];
            let a = points[1][3];
            let b = points[1][2];
            factors[1][0] =
                [K::ONE.sub(a).mul(K::ONE.sub(b)), a.mul(K::ONE.sub(b)),
                        K::ONE.sub(a).mul(b), a.mul(b)];
            let a = points[1][1];
            let b = points[1][0];
            factors[1][1] =
                [K::ONE.sub(a).mul(K::ONE.sub(b)), a.mul(K::ONE.sub(b)),
                        K::ONE.sub(a).mul(b), a.mul(b)];
            let a = points[1][5];
            let b = points[1][4];
            factors[1][2] =
                [K::ONE.sub(a).mul(K::ONE.sub(b)), a.mul(K::ONE.sub(b)),
                        K::ONE.sub(a).mul(b), a.mul(b)];
            let a = points[1][9];
            let b = points[1][8];
            factors[1][3] =
                [K::ONE.sub(a).mul(K::ONE.sub(b)), a.mul(K::ONE.sub(b)),
                        K::ONE.sub(a).mul(b), a.mul(b)];
            let a = points[1][7];
            let b = points[1][6];
            factors[1][4] =
                [K::ONE.sub(a).mul(K::ONE.sub(b)), a.mul(K::ONE.sub(b)),
                        K::ONE.sub(a).mul(b), a.mul(b)];
            let a = points[2][3];
            let b = points[2][2];
            factors[2][0] =
                [K::ONE.sub(a).mul(K::ONE.sub(b)), a.mul(K::ONE.sub(b)),
                        K::ONE.sub(a).mul(b), a.mul(b)];
            let a = points[2][1];
            let b = points[2][0];
            factors[2][1] =
                [K::ONE.sub(a).mul(K::ONE.sub(b)), a.mul(K::ONE.sub(b)),
                        K::ONE.sub(a).mul(b), a.mul(b)];
            let a = points[2][5];
            let b = points[2][4];
            factors[2][2] =
                [K::ONE.sub(a).mul(K::ONE.sub(b)), a.mul(K::ONE.sub(b)),
                        K::ONE.sub(a).mul(b), a.mul(b)];
            let a = points[2][9];
            let b = points[2][8];
            factors[2][3] =
                [K::ONE.sub(a).mul(K::ONE.sub(b)), a.mul(K::ONE.sub(b)),
                        K::ONE.sub(a).mul(b), a.mul(b)];
            let a = points[2][7];
            let b = points[2][6];
            factors[2][4] =
                [K::ONE.sub(a).mul(K::ONE.sub(b)), a.mul(K::ONE.sub(b)),
                        K::ONE.sub(a).mul(b), a.mul(b)];
            factors[3][0] = [K::ONE, z[0].y, z[0].x, z[0].x.mul(z[0].y)];
            let mut x = double(z[0].x);
            let y = double(x);
            factors[3][1] = [K::ONE, x, y, x.mul(y)];
            x = double(y);
            let y = double(x);
            factors[3][2] = [K::ONE, x, y, x.mul(y)];
            x = double(y);
            let y = double(x);
            factors[3][3] = [K::ONE, x, y, x.mul(y)];
            x = double(y);
            let y = double(x);
            factors[3][4] = [K::ONE, x, y, x.mul(y)];
            x = double(y);
            factors[4][0] = [K::ONE, z[1].y, z[1].x, z[1].x.mul(z[1].y)];
            let mut x = double(z[1].x);
            let y = double(x);
            factors[4][1] = [K::ONE, x, y, x.mul(y)];
            x = double(y);
            let y = double(x);
            factors[4][2] = [K::ONE, x, y, x.mul(y)];
            x = double(y);
            let y = double(x);
            factors[4][3] = [K::ONE, x, y, x.mul(y)];
            x = double(y);
            let y = double(x);
            factors[4][4] = [K::ONE, x, y, x.mul(y)];
            x = double(y);
            Ok(Weights { variant, factors, points, extra })
        }
        pub fn raw(&self, kind: usize, j: usize) -> K {
            raw_value(*self, kind, j)
        }
        /// The caller owns allocation and retains Error::Allocation before this kernel.
        pub fn materialize(&self, kappa: E, w: &mut [E; 1024])
            -> Result<(), Error> {
            let out = materialize_values(*self, kappa, *w);
            *w = out;
            Ok(())
        }
    }
    type Powers7 = (E, E, E, E, E, E, E);
    fn powers7(x: E) -> Powers7 {
        let p = crate::prover_powers::powers::<7>(x);
        (p[0], p[1], p[2], p[3], p[4], p[5], p[6])
    }
    fn materialize_cell(weights: Weights, k: Powers7, j: usize) -> E {
        let mut v = E::ZERO;
        v = v.add(mul_qm31(k.0, raw_value(weights, 0, j)));
        v = v.add(mul_qm31(k.1, raw_value(weights, 1, j)));
        v = v.add(mul_qm31(k.2, raw_value(weights, 2, j)));
        v = v.add(mul_qm31(k.3, raw_value(weights, 3, j)));
        v = v.add(mul_qm31(k.4, raw_value(weights, 4, j)));
        v = v.add(mul_qm31(k.5, raw_value(weights, 5, j)));
        v = v.add(mul_qm31(k.6, raw_value(weights, 6, j)));
        v
    }
    fn materialize_values(weights: Weights, kappa: E, mut out: [E; 1024])
        -> [E; 1024] {
        let k = powers7(kappa);
        let mut j = 0usize;
        while j < 1024 { out[j] = materialize_cell(weights, k, j); j += 1; }
        out
    }
    const HOST_COEFFICIENT_TO_ROW: [u16; 1024] =
        [13, 14, 15, 29, 30, 31, 45, 46, 47, 61, 62, 63, 77, 78, 79, 93, 94,
                95, 109, 110, 111, 125, 126, 127, 141, 142, 143, 157, 158,
                159, 173, 174, 175, 189, 190, 191, 205, 206, 207, 221, 222,
                223, 237, 238, 239, 253, 254, 255, 269, 270, 271, 285, 286,
                287, 301, 302, 303, 317, 318, 319, 333, 334, 335, 349, 350,
                351, 365, 366, 367, 381, 382, 383, 397, 398, 399, 413, 414,
                415, 429, 430, 431, 445, 446, 447, 461, 462, 463, 477, 478, 0,
                1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 16, 17, 18, 19, 20, 21,
                22, 23, 24, 25, 26, 27, 28, 32, 33, 34, 35, 36, 37, 38, 39,
                40, 41, 42, 43, 44, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57,
                58, 59, 60, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75,
                76, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 96,
                97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 112,
                113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124,
                128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139,
                140, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154,
                155, 156, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169,
                170, 171, 172, 176, 177, 178, 179, 180, 181, 182, 183, 184,
                185, 186, 187, 188, 192, 193, 194, 195, 196, 197, 198, 199,
                200, 201, 202, 203, 204, 208, 209, 210, 211, 212, 213, 214,
                215, 216, 217, 218, 219, 220, 224, 225, 226, 227, 228, 229,
                230, 231, 232, 233, 234, 235, 236, 240, 241, 242, 243, 244,
                245, 246, 247, 248, 249, 250, 251, 252, 256, 257, 258, 259,
                260, 261, 262, 263, 264, 265, 266, 267, 268, 272, 273, 274,
                275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 288, 289,
                290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 304,
                305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316,
                320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331,
                332, 336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346,
                347, 348, 352, 353, 354, 355, 356, 357, 358, 359, 360, 361,
                362, 363, 364, 368, 369, 370, 371, 372, 373, 374, 375, 376,
                377, 378, 379, 380, 384, 385, 386, 387, 388, 389, 390, 391,
                392, 393, 394, 395, 396, 400, 401, 402, 403, 404, 405, 406,
                407, 408, 409, 410, 411, 412, 416, 417, 418, 419, 420, 421,
                422, 423, 424, 425, 426, 427, 428, 432, 433, 434, 435, 436,
                437, 438, 439, 440, 441, 442, 443, 444, 448, 449, 450, 451,
                452, 453, 454, 455, 456, 457, 458, 459, 460, 464, 465, 466,
                467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 479, 480,
                481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492,
                493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 503, 504,
                505, 506, 507, 508, 509, 510, 511, 512, 513, 514, 515, 516,
                517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527, 528,
                529, 530, 531, 532, 533, 534, 535, 536, 537, 538, 539, 540,
                541, 542, 543, 544, 545, 546, 547, 548, 549, 550, 551, 552,
                553, 554, 555, 556, 557, 558, 559, 560, 561, 562, 563, 564,
                565, 566, 567, 568, 569, 570, 571, 572, 573, 574, 575, 576,
                577, 578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588,
                589, 590, 591, 592, 593, 594, 595, 596, 597, 598, 599, 600,
                601, 602, 603, 604, 605, 606, 607, 608, 609, 610, 611, 612,
                613, 614, 615, 616, 617, 618, 619, 620, 621, 622, 623, 624,
                625, 626, 627, 628, 629, 630, 631, 632, 633, 634, 635, 636,
                637, 638, 639, 640, 641, 642, 643, 644, 645, 646, 647, 648,
                649, 650, 651, 652, 653, 654, 655, 656, 657, 658, 659, 660,
                661, 662, 663, 664, 665, 666, 667, 668, 669, 670, 671, 672,
                673, 674, 675, 676, 677, 678, 679, 680, 681, 682, 683, 684,
                685, 686, 687, 688, 689, 690, 691, 692, 693, 694, 695, 696,
                697, 698, 699, 700, 701, 702, 703, 704, 705, 706, 707, 708,
                709, 710, 711, 712, 713, 714, 715, 716, 717, 718, 719, 720,
                721, 722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732,
                733, 734, 735, 736, 737, 738, 739, 740, 741, 742, 743, 744,
                745, 746, 747, 748, 749, 750, 751, 752, 753, 754, 755, 756,
                757, 758, 759, 760, 761, 762, 763, 764, 765, 766, 767, 768,
                769, 770, 771, 772, 773, 774, 775, 776, 777, 778, 779, 780,
                781, 782, 783, 784, 785, 786, 787, 788, 789, 790, 791, 792,
                793, 794, 795, 796, 797, 798, 799, 800, 801, 802, 803, 804,
                805, 806, 807, 808, 809, 810, 811, 812, 813, 814, 815, 816,
                817, 818, 819, 820, 821, 822, 823, 824, 825, 826, 827, 828,
                829, 830, 831, 832, 833, 834, 835, 836, 837, 838, 839, 840,
                841, 842, 843, 844, 845, 846, 847, 848, 849, 850, 851, 852,
                853, 854, 855, 856, 857, 858, 859, 860, 861, 862, 863, 864,
                865, 866, 867, 868, 869, 870, 871, 872, 873, 874, 875, 876,
                877, 878, 879, 880, 881, 882, 883, 884, 885, 886, 887, 888,
                889, 890, 891, 892, 893, 894, 895, 896, 897, 898, 899, 900,
                901, 902, 903, 904, 905, 906, 907, 908, 909, 910, 911, 912,
                913, 914, 915, 916, 917, 918, 919, 920, 921, 922, 923, 924,
                925, 926, 927, 928, 929, 930, 931, 932, 933, 934, 935, 936,
                937, 938, 939, 940, 941, 942, 943, 944, 945, 946, 947, 948,
                949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959, 960,
                961, 962, 963, 964, 965, 966, 967, 968, 969, 970, 971, 972,
                973, 974, 975, 976, 977, 978, 979, 980, 981, 982, 983, 984,
                985, 986, 987, 988, 989, 990, 991, 992, 993, 994, 995, 996,
                997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007,
                1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017,
                1018, 1019, 1020, 1021, 1022, 1023];
    fn host_row(variant: Variant, j: usize) -> usize {
        if let Variant::D = variant {
            return HOST_COEFFICIENT_TO_ROW[j] as usize;
        }
        let mut out = 0usize;
        let mut d = 0usize;
        while d < 5 {
            out |=
                ((j >> ((2 * d) as u32)) & 3) <<
                    ((2 * crate::transport::TAU[d]) as u32);
            d += 1;
        }
        out
    }
    fn raw_value(weights: Weights, kind: usize, j: usize) -> K {
        if kind == 0 {
            let r = host_row(weights.variant, j);
            return if (aspis_core::r0::opening::COPY_ACTIVE_ROW_MASKS[r / 16]
                                    >> (r % 16)) & 1 == 0 {
                    K::ONE
                } else { K::ZERO };
        }
        if kind == 4 {
            if j < 56 { return weights.extra[j / 28].pow((j % 28) as u64); }
            return K::ZERO;
        }
        if kind >= 1 && kind <= 3 && weights.variant == Variant::D {
            let r = host_row(weights.variant, j);
            return point_raw(weights.points[kind - 1], r);
        }
        let k = if kind < 4 { kind - 1 } else { kind - 2 };
        tensor_raw(weights.factors[k], j)
    }
    fn point_factor(point: K, r: usize, b: u32) -> K {
        if r & (1usize << b) == 0 { K::ONE.sub(point) } else { point }
    }
    fn point_raw(points: [K; 10], r: usize) -> K {
        let mut v = K::ONE;
        v = v.mul(point_factor(points[9], r, 0));
        v = v.mul(point_factor(points[8], r, 1));
        v = v.mul(point_factor(points[7], r, 2));
        v = v.mul(point_factor(points[6], r, 3));
        v = v.mul(point_factor(points[5], r, 4));
        v = v.mul(point_factor(points[4], r, 5));
        v = v.mul(point_factor(points[3], r, 6));
        v = v.mul(point_factor(points[2], r, 7));
        v = v.mul(point_factor(points[1], r, 8));
        v = v.mul(point_factor(points[0], r, 9));
        v
    }
    fn tensor_raw(factors: [[K; 4]; 5], j: usize) -> K {
        let mut v = K::ONE;
        v = v.mul(factors[0][(j >> 0u32) & 3]);
        v = v.mul(factors[1][(j >> 2u32) & 3]);
        v = v.mul(factors[2][(j >> 4u32) & 3]);
        v = v.mul(factors[3][(j >> 6u32) & 3]);
        v = v.mul(factors[4][(j >> 8u32) & 3]);
        v
    }
    fn mul_qm31(x: E, rhs: K) -> E {
        use aspis_core::field::{CM31, M31, ct};
        let rhs =
            K {
                c0: CM31 {
                    a: M31(ct::reduce64(rhs.c0.a.0 as u64)),
                    b: M31(ct::reduce64(rhs.c0.b.0 as u64)),
                },
                c1: CM31 {
                    a: M31(ct::reduce64(rhs.c1.a.0 as u64)),
                    b: M31(ct::reduce64(rhs.c1.b.0 as u64)),
                },
            };
        let a = x.c0().mul(rhs);
        let b = x.c1().mul(rhs);
        E::from_limbs([a.c0.a.0, a.c0.b.0, a.c1.a.0, a.c1.b.0, b.c0.a.0,
                        b.c0.b.0, b.c1.a.0, b.c1.b.0]).unwrap()
    }
}
pub use aspis_prover::host_forest;
pub mod host_multilinear {
    //! Drop-free prover-local sparse multilinear evaluation. The field operation
    //! order, literal Boolean suffix test and wrong-length rejection are retained.
    use aspis_core::field::QM31;
    pub struct SparseWeights {
        pub data: [(usize, QM31); 1024],
        pub len: usize,
    }
    #[automatically_derived]
    #[doc(hidden)]
    unsafe impl ::core::clone::TrivialClone for SparseWeights { }
    #[automatically_derived]
    impl ::core::clone::Clone for SparseWeights {
        #[inline]
        fn clone(&self) -> SparseWeights {
            let _: ::core::clone::AssertParamIsClone<[(usize, QM31); 1024]>;
            let _: ::core::clone::AssertParamIsClone<usize>;
            *self
        }
    }
    #[automatically_derived]
    impl ::core::marker::Copy for SparseWeights { }
    pub fn sparse_eq_weights(point: &[QM31; 10]) -> SparseWeights {
        let mut prefix_len = 10usize;
        while prefix_len > 0 &&
                (point[prefix_len - 1] == QM31::ZERO ||
                        point[prefix_len - 1] == QM31::ONE) {
            prefix_len -= 1;
        }
        let trailing_boolean = 10 - prefix_len;
        let mut suffix = 0usize;
        let mut coordinate = prefix_len;
        while coordinate < 10 {
            suffix =
                (suffix << 1u32) |
                    usize::from(point[coordinate] == QM31::ONE);
            coordinate += 1;
        }
        let mut output =
            SparseWeights {
                data: [(0, QM31::ZERO); 1024],
                len: 1usize << prefix_len,
            };
        let mut prefix = 0usize;
        while prefix < output.len {
            let row = (prefix << trailing_boolean) | suffix;
            let mut weight = QM31::ONE;
            let mut coordinate = 0usize;
            while coordinate < prefix_len {
                let bit = (prefix >> (prefix_len - 1 - coordinate)) & 1;
                weight =
                    weight.mul(if bit == 0 {
                            QM31::ONE.sub(point[coordinate])
                        } else { point[coordinate] });
                coordinate += 1;
            }
            output.data[prefix] = (row, weight);
            prefix += 1;
        }
        output
    }
    pub fn multilinear_evaluate_qm31(column: &[QM31], point: &[QM31; 10])
        -> Option<QM31> {
        if column.len() != 1024 { return None; }
        let weights = sparse_eq_weights(point);
        let mut sum = QM31::ZERO;
        let mut i = 0usize;
        while i < weights.len {
            let (row, weight) = sparse_weight_at(&weights, i);
            sum = sum.add(weight.mul(column[row]));
            i += 1;
        }
        Some(sum)
    }
    #[inline(never)]
    fn sparse_weight_at(weights: &SparseWeights, i: usize) -> (usize, QM31) {
        weights.data[i]
    }
}
mod host_copy_terminal {
    //! Allocation-bounded SBF-safe Copy lane for the eight-lane Pool V1
    //! pair-forest relation.
    //!
    //! Runtime evaluation consumes only generated patterns, endpoints and fixed
    //! active-row masks. The allocation-heavy typed registry remains the
    //! independent host compiler/reference boundary and is not linked on SBF.
    macro_rules! qm31_array {
        ($n:expr, $index:ident, $body:expr) =>
        {{
                let mut output = [QM31::ZERO; $n]; let mut $index = 0usize;
                while $index < $n { output[$index] = $body; $index += 1; }
                output
            }};
    }
    use crate::host_terminal_field::PreparedQm31Multiplier;
    use aspis_core::field::{CM31, M31, QM31};
    use aspis_statement::poseidon2::POSEIDON2_WIDTH;
    pub const POOL_V1_PAIR_FOREST_COPY_TERMINAL_ROWS_V1: usize = 1024;
    pub const POOL_V1_PAIR_FOREST_COPY_TERMINAL_COLUMNS_V1: usize = 16;
    pub const POOL_V1_PAIR_FOREST_COPY_TERMINAL_LINKS_V1: usize = 136;
    pub const POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1: usize = 14;
    pub const POOL_V1_PAIR_FOREST_COPY_TERMINAL_FIXED_HEAP_ALLOCATIONS_V1:
        usize =
        if false { 2 } else { 1 };
    pub const POOL_V1_PAIR_FOREST_COPY_TERMINAL_SELECTOR_HEAP_BYTES_V1: usize
        =
        core::mem::size_of::<Selectors>();
    pub const POOL_V1_PAIR_FOREST_COPY_TERMINAL_TENSOR_HEAP_BYTES_V1: usize =
        if false { 103 * core::mem::size_of::<QM31>() } else { 0 };
    pub const POOL_V1_PAIR_FOREST_COPY_TERMINAL_FIXED_HEAP_BYTES_V1: usize =
        POOL_V1_PAIR_FOREST_COPY_TERMINAL_SELECTOR_HEAP_BYTES_V1 +
            POOL_V1_PAIR_FOREST_COPY_TERMINAL_TENSOR_HEAP_BYTES_V1;
    pub const
        PINNED_POOL_V1_PAIR_FOREST_COPY_TERMINAL_ACTIVE_ROWS_FINGERPRINT_V1:
        u64 =
        constants::ACTIVE_ROWS_FINGERPRINT;
    /// Exact SBF-safe active-row schedule consumed by the selected verifier.
    /// Host generation tests independently replay it from the typed tuple registry.
    pub fn pool_v1_pair_forest_copy_active_row_masks_compiled_v1()
        -> &'static [u16; 64] {
        &constants::ACTIVE_ROW_MASKS
    }
    /// Frozen row-to-group schedule generated from the exact pair-forest copy
    /// registry.  The selected verifier consumes this directly instead of
    /// rebuilding and deduplicating public layout data on every transaction.
    pub fn pool_v1_pair_forest_copy_inactive_row_groups_compiled_v1()
        -> &'static [u8; 64] {
        &constants::INACTIVE_ROW_GROUPS
    }
    /// Deduplicated inactive masks referenced by
    /// [`pool_v1_pair_forest_copy_inactive_row_groups_compiled_v1`].
    pub fn pool_v1_pair_forest_copy_inactive_group_masks_compiled_v1()
        -> &'static [u16] {
        &constants::INACTIVE_GROUP_MASKS
    }
    const _: () =
        if !(POSEIDON2_WIDTH == POOL_V1_PAIR_FOREST_COPY_TERMINAL_COLUMNS_V1)
            {
            ::core::panicking::panic("assertion failed: POSEIDON2_WIDTH == POOL_V1_PAIR_FOREST_COPY_TERMINAL_COLUMNS_V1")
        };
    const _: () =
        if !(constants::COPY_LINKS.len() ==
                    POOL_V1_PAIR_FOREST_COPY_TERMINAL_LINKS_V1) {
            ::core::panicking::panic("assertion failed: constants::COPY_LINKS.len() == POOL_V1_PAIR_FOREST_COPY_TERMINAL_LINKS_V1")
        };
    const _: () =
        if !(constants::COPY_PATTERNS.len() ==
                    POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1) {
            ::core::panicking::panic("assertion failed: constants::COPY_PATTERNS.len() ==\n    POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1")
        };
    const _: () =
        if !(constants::ACTIVE_ROW_MASKS.len() == 64) {
            ::core::panicking::panic("assertion failed: constants::ACTIVE_ROW_MASKS.len() == 64")
        };
    const _: () =
        if !(constants::INACTIVE_ROW_GROUPS.len() == 64) {
            ::core::panicking::panic("assertion failed: constants::INACTIVE_ROW_GROUPS.len() == 64")
        };
    const _: () =
        if !(constants::INACTIVE_GROUP_MASKS.len() <= 64) {
            ::core::panicking::panic("assertion failed: constants::INACTIVE_GROUP_MASKS.len() <= 64")
        };
    pub enum PoolV1PairForestCompiledVariantV1 {
        PrivateTransfer,
        Withdrawal,
    }
    #[automatically_derived]
    #[doc(hidden)]
    unsafe impl ::core::clone::TrivialClone for
        PoolV1PairForestCompiledVariantV1 {
    }
    #[automatically_derived]
    impl ::core::clone::Clone for PoolV1PairForestCompiledVariantV1 {
        #[inline]
        fn clone(&self) -> PoolV1PairForestCompiledVariantV1 { *self }
    }
    #[automatically_derived]
    impl ::core::marker::Copy for PoolV1PairForestCompiledVariantV1 { }
    #[automatically_derived]
    impl ::core::fmt::Debug for PoolV1PairForestCompiledVariantV1 {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            ::core::fmt::Formatter::write_str(f,
                match self {
                    PoolV1PairForestCompiledVariantV1::PrivateTransfer =>
                        "PrivateTransfer",
                    PoolV1PairForestCompiledVariantV1::Withdrawal =>
                        "Withdrawal",
                })
        }
    }
    #[automatically_derived]
    impl ::core::marker::StructuralPartialEq for
        PoolV1PairForestCompiledVariantV1 {
    }
    #[automatically_derived]
    impl ::core::cmp::PartialEq for PoolV1PairForestCompiledVariantV1 {
        #[inline]
        fn eq(&self, other: &PoolV1PairForestCompiledVariantV1) -> bool {
            let __self_discr = ::core::intrinsics::discriminant_value(self);
            let __arg1_discr = ::core::intrinsics::discriminant_value(other);
            __self_discr == __arg1_discr
        }
    }
    #[automatically_derived]
    impl ::core::cmp::Eq for PoolV1PairForestCompiledVariantV1 {
        #[inline]
        #[doc(hidden)]
        #[coverage(off)]
        fn assert_fields_are_eq(&self) {}
    }
    pub struct PoolV1PairForestCompiledCopyTerminalV1 {
        pub residual: QM31,
        pub active: QM31,
    }
    #[automatically_derived]
    #[doc(hidden)]
    unsafe impl ::core::clone::TrivialClone for
        PoolV1PairForestCompiledCopyTerminalV1 {
    }
    #[automatically_derived]
    impl ::core::clone::Clone for PoolV1PairForestCompiledCopyTerminalV1 {
        #[inline]
        fn clone(&self) -> PoolV1PairForestCompiledCopyTerminalV1 {
            let _: ::core::clone::AssertParamIsClone<QM31>;
            *self
        }
    }
    #[automatically_derived]
    impl ::core::marker::Copy for PoolV1PairForestCompiledCopyTerminalV1 { }
    #[automatically_derived]
    impl ::core::fmt::Debug for PoolV1PairForestCompiledCopyTerminalV1 {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            ::core::fmt::Formatter::debug_struct_field2_finish(f,
                "PoolV1PairForestCompiledCopyTerminalV1", "residual",
                &self.residual, "active", &&self.active)
        }
    }
    #[automatically_derived]
    impl ::core::marker::StructuralPartialEq for
        PoolV1PairForestCompiledCopyTerminalV1 {
    }
    #[automatically_derived]
    impl ::core::cmp::PartialEq for PoolV1PairForestCompiledCopyTerminalV1 {
        #[inline]
        fn eq(&self, other: &PoolV1PairForestCompiledCopyTerminalV1) -> bool {
            self.residual == other.residual && self.active == other.active
        }
    }
    #[automatically_derived]
    impl ::core::cmp::Eq for PoolV1PairForestCompiledCopyTerminalV1 {
        #[inline]
        #[doc(hidden)]
        #[coverage(off)]
        fn assert_fields_are_eq(&self) {
            let _: ::core::cmp::AssertParamIsEq<QM31>;
        }
    }
    struct CompiledPoolV1PairForestPattern {
        /// 0 = zero, 1 = row-local C1 cell plus a canonical M31 offset.
        kinds: [u8; POSEIDON2_WIDTH],
        columns: [u8; POSEIDON2_WIDTH],
        offsets: [u32; POSEIDON2_WIDTH],
    }
    #[automatically_derived]
    #[doc(hidden)]
    unsafe impl ::core::clone::TrivialClone for
        CompiledPoolV1PairForestPattern {
    }
    #[automatically_derived]
    impl ::core::clone::Clone for CompiledPoolV1PairForestPattern {
        #[inline]
        fn clone(&self) -> CompiledPoolV1PairForestPattern {
            let _: ::core::clone::AssertParamIsClone<[u8; POSEIDON2_WIDTH]>;
            let _: ::core::clone::AssertParamIsClone<[u8; POSEIDON2_WIDTH]>;
            let _: ::core::clone::AssertParamIsClone<[u32; POSEIDON2_WIDTH]>;
            *self
        }
    }
    #[automatically_derived]
    impl ::core::marker::Copy for CompiledPoolV1PairForestPattern { }
    struct CompiledPoolV1PairForestEndpoint {
        row: u16,
        slot: u8,
        pattern: u8,
    }
    #[automatically_derived]
    #[doc(hidden)]
    unsafe impl ::core::clone::TrivialClone for
        CompiledPoolV1PairForestEndpoint {
    }
    #[automatically_derived]
    impl ::core::clone::Clone for CompiledPoolV1PairForestEndpoint {
        #[inline]
        fn clone(&self) -> CompiledPoolV1PairForestEndpoint {
            let _: ::core::clone::AssertParamIsClone<u16>;
            let _: ::core::clone::AssertParamIsClone<u8>;
            *self
        }
    }
    #[automatically_derived]
    impl ::core::marker::Copy for CompiledPoolV1PairForestEndpoint { }
    struct CompiledPoolV1PairForestLink {
        tag: u32,
        /// 0 = one, 1 = transfer, 2 = withdrawal, 3 = append-left,
        /// 4 = append-right.
        weight_kind: u8,
        weight_level: u8,
        producer: CompiledPoolV1PairForestEndpoint,
        consumer: CompiledPoolV1PairForestEndpoint,
    }
    #[automatically_derived]
    #[doc(hidden)]
    unsafe impl ::core::clone::TrivialClone for CompiledPoolV1PairForestLink {
    }
    #[automatically_derived]
    impl ::core::clone::Clone for CompiledPoolV1PairForestLink {
        #[inline]
        fn clone(&self) -> CompiledPoolV1PairForestLink {
            let _: ::core::clone::AssertParamIsClone<u32>;
            let _: ::core::clone::AssertParamIsClone<u8>;
            let _:
                    ::core::clone::AssertParamIsClone<CompiledPoolV1PairForestEndpoint>;
            *self
        }
    }
    #[automatically_derived]
    impl ::core::marker::Copy for CompiledPoolV1PairForestLink { }
    mod constants {
        use super::{
            CompiledPoolV1PairForestEndpoint, CompiledPoolV1PairForestLink,
            CompiledPoolV1PairForestPattern,
        };
        pub(crate) const ACTIVE_ROWS_FINGERPRINT: u64 = 0xdf394a5a8554d09c;
        pub(crate) const ACTIVE_ROW_MASKS: [u16; 64] =
            [6144, 6144, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145,
                    6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145,
                    6145, 6145, 6145, 6145, 6144, 4097, 2048, 6145, 2049, 2048,
                    6145, 2049, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145,
                    6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145,
                    6145, 6145, 4097, 6145, 6145, 4097, 26214, 26214, 26214,
                    26214, 26214, 26214, 1749];
        pub(crate) const INACTIVE_ROW_GROUPS: [u8; 64] =
            [0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
                    1, 1, 1, 0, 2, 3, 1, 4, 3, 1, 4, 1, 1, 1, 1, 1, 1, 1, 1, 1,
                    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 5, 5, 5, 5,
                    5, 6];
        pub(crate) const INACTIVE_GROUP_MASKS: [u16; 7] =
            [59391, 59390, 61438, 63487, 63486, 39321, 63786];
        pub(crate) const COPY_PATTERNS: [CompiledPoolV1PairForestPattern; 14]
            =
            [CompiledPoolV1PairForestPattern {
                        kinds: [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
                        columns: [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14,
                                15],
                        offsets: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                    },
                    CompiledPoolV1PairForestPattern {
                        kinds: [1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
                        columns: [0, 1, 2, 3, 4, 5, 6, 7, 0, 0, 0, 0, 0, 0, 0, 0],
                        offsets: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                    },
                    CompiledPoolV1PairForestPattern {
                        kinds: [1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                        columns: [2, 3, 4, 5, 6, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                        offsets: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                    },
                    CompiledPoolV1PairForestPattern {
                        kinds: [1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                        columns: [0, 1, 2, 3, 4, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                        offsets: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                    },
                    CompiledPoolV1PairForestPattern {
                        kinds: [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                        columns: [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                        offsets: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                    },
                    CompiledPoolV1PairForestPattern {
                        kinds: [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                        columns: [6, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                        offsets: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                    },
                    CompiledPoolV1PairForestPattern {
                        kinds: [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                        columns: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                        offsets: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                    },
                    CompiledPoolV1PairForestPattern {
                        kinds: [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                        columns: [10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                        offsets: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                    },
                    CompiledPoolV1PairForestPattern {
                        kinds: [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                        columns: [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                        offsets: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                    },
                    CompiledPoolV1PairForestPattern {
                        kinds: [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                        columns: [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                        offsets: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                    },
                    CompiledPoolV1PairForestPattern {
                        kinds: [1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
                        columns: [8, 9, 10, 11, 12, 13, 14, 15, 0, 0, 0, 0, 0, 0, 0,
                                0],
                        offsets: [0, 0, 0, 0, 0, 0, 0, 1051521018, 0, 0, 0, 0, 0, 0,
                                0, 0],
                    },
                    CompiledPoolV1PairForestPattern {
                        kinds: [1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
                        columns: [2, 3, 4, 5, 6, 7, 8, 9, 0, 0, 0, 0, 0, 0, 0, 0],
                        offsets: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                    },
                    CompiledPoolV1PairForestPattern {
                        kinds: [1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
                        columns: [1, 2, 3, 4, 5, 6, 7, 8, 0, 0, 0, 0, 0, 0, 0, 0],
                        offsets: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                    },
                    CompiledPoolV1PairForestPattern {
                        kinds: [1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
                        columns: [8, 9, 10, 11, 12, 13, 14, 15, 0, 0, 0, 0, 0, 0, 0,
                                0],
                        offsets: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                    }];
        pub(crate) const COPY_LINKS: [CompiledPoolV1PairForestLink; 136] =
            [CompiledPoolV1PairForestLink {
                        tag: 1124073472,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 27,
                            slot: 0,
                            pattern: 0,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 32,
                            slot: 0,
                            pattern: 0,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073473,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 43,
                            slot: 0,
                            pattern: 0,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 48,
                            slot: 0,
                            pattern: 0,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073474,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 411,
                            slot: 0,
                            pattern: 0,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 416,
                            slot: 0,
                            pattern: 0,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073475,
                        weight_kind: 1,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 443,
                            slot: 0,
                            pattern: 0,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 448,
                            slot: 0,
                            pattern: 0,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073476,
                        weight_kind: 1,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 459,
                            slot: 0,
                            pattern: 0,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 464,
                            slot: 0,
                            pattern: 0,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073477,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 491,
                            slot: 0,
                            pattern: 0,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 496,
                            slot: 0,
                            pattern: 0,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073478,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 507,
                            slot: 0,
                            pattern: 0,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 512,
                            slot: 0,
                            pattern: 0,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073479,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 11,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 28,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073480,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 12,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 412,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073481,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 44,
                            slot: 0,
                            pattern: 2,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 428,
                            slot: 0,
                            pattern: 3,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073482,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 60,
                            slot: 0,
                            pattern: 4,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 428,
                            slot: 1,
                            pattern: 5,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073483,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 44,
                            slot: 1,
                            pattern: 6,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 1008,
                            slot: 0,
                            pattern: 7,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073484,
                        weight_kind: 1,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 460,
                            slot: 0,
                            pattern: 6,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 1010,
                            slot: 0,
                            pattern: 7,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073485,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 508,
                            slot: 0,
                            pattern: 6,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 1012,
                            slot: 0,
                            pattern: 7,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073486,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 1008,
                            slot: 0,
                            pattern: 7,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 1014,
                            slot: 0,
                            pattern: 6,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073487,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 1010,
                            slot: 0,
                            pattern: 7,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 1014,
                            slot: 1,
                            pattern: 8,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073488,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 1012,
                            slot: 0,
                            pattern: 7,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 1015,
                            slot: 0,
                            pattern: 8,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073489,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 1014,
                            slot: 0,
                            pattern: 9,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 1015,
                            slot: 1,
                            pattern: 6,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073490,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 64,
                            slot: 0,
                            pattern: 10,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 1017,
                            slot: 0,
                            pattern: 11,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073491,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 913,
                            slot: 0,
                            pattern: 6,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 1017,
                            slot: 1,
                            pattern: 7,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073492,
                        weight_kind: 1,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 523,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 1018,
                            slot: 0,
                            pattern: 11,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073493,
                        weight_kind: 1,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 475,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 540,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073494,
                        weight_kind: 2,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 523,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 540,
                            slot: 1,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073495,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 1018,
                            slot: 0,
                            pattern: 11,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 528,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073496,
                        weight_kind: 3,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 539,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 556,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073497,
                        weight_kind: 4,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 539,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 544,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073498,
                        weight_kind: 3,
                        weight_level: 1,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 555,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 572,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073499,
                        weight_kind: 4,
                        weight_level: 1,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 555,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 560,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073500,
                        weight_kind: 3,
                        weight_level: 2,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 571,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 588,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073501,
                        weight_kind: 4,
                        weight_level: 2,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 571,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 576,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073502,
                        weight_kind: 3,
                        weight_level: 3,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 587,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 604,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073503,
                        weight_kind: 4,
                        weight_level: 3,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 587,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 592,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073504,
                        weight_kind: 3,
                        weight_level: 4,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 603,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 620,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073505,
                        weight_kind: 4,
                        weight_level: 4,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 603,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 608,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073506,
                        weight_kind: 3,
                        weight_level: 5,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 619,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 636,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073507,
                        weight_kind: 4,
                        weight_level: 5,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 619,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 624,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073508,
                        weight_kind: 3,
                        weight_level: 6,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 635,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 652,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073509,
                        weight_kind: 4,
                        weight_level: 6,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 635,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 640,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073510,
                        weight_kind: 3,
                        weight_level: 7,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 651,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 668,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073511,
                        weight_kind: 4,
                        weight_level: 7,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 651,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 656,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073512,
                        weight_kind: 3,
                        weight_level: 8,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 667,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 684,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073513,
                        weight_kind: 4,
                        weight_level: 8,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 667,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 672,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073514,
                        weight_kind: 3,
                        weight_level: 9,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 683,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 700,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073515,
                        weight_kind: 4,
                        weight_level: 9,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 683,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 688,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073516,
                        weight_kind: 3,
                        weight_level: 10,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 699,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 716,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073517,
                        weight_kind: 4,
                        weight_level: 10,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 699,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 704,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073518,
                        weight_kind: 3,
                        weight_level: 11,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 715,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 732,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073519,
                        weight_kind: 4,
                        weight_level: 11,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 715,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 720,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073520,
                        weight_kind: 3,
                        weight_level: 12,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 731,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 748,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073521,
                        weight_kind: 4,
                        weight_level: 12,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 731,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 736,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073522,
                        weight_kind: 3,
                        weight_level: 13,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 747,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 764,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073523,
                        weight_kind: 4,
                        weight_level: 13,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 747,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 752,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073524,
                        weight_kind: 3,
                        weight_level: 14,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 763,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 780,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073525,
                        weight_kind: 4,
                        weight_level: 14,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 763,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 768,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073526,
                        weight_kind: 3,
                        weight_level: 15,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 779,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 796,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073527,
                        weight_kind: 4,
                        weight_level: 15,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 779,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 784,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073528,
                        weight_kind: 3,
                        weight_level: 16,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 795,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 812,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073529,
                        weight_kind: 4,
                        weight_level: 16,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 795,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 800,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073530,
                        weight_kind: 3,
                        weight_level: 17,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 811,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 828,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073531,
                        weight_kind: 4,
                        weight_level: 17,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 811,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 816,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073532,
                        weight_kind: 3,
                        weight_level: 18,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 827,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 844,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073533,
                        weight_kind: 4,
                        weight_level: 18,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 827,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 832,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073534,
                        weight_kind: 3,
                        weight_level: 19,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 843,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 860,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073535,
                        weight_kind: 4,
                        weight_level: 19,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 843,
                            slot: 1,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 848,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073536,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 59,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 913,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073537,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 914,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 76,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073538,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 914,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 64,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073539,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 75,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 917,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073540,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 918,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 92,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073541,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 918,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 80,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073542,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 91,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 921,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073543,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 922,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 108,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073544,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 922,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 96,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073545,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 107,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 925,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073546,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 926,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 124,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073547,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 926,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 112,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073548,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 123,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 929,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073549,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 930,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 140,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073550,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 930,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 128,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073551,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 139,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 933,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073552,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 934,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 156,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073553,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 934,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 144,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073554,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 155,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 937,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073555,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 938,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 172,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073556,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 938,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 160,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073557,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 171,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 941,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073558,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 942,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 188,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073559,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 942,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 176,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073560,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 187,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 945,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073561,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 946,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 204,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073562,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 946,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 192,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073563,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 203,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 949,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073564,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 950,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 220,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073565,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 950,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 208,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073566,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 219,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 953,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073567,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 954,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 236,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073568,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 954,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 224,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073569,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 235,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 957,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073570,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 958,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 252,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073571,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 958,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 240,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073572,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 251,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 961,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073573,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 962,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 268,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073574,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 962,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 256,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073575,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 267,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 965,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073576,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 966,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 284,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073577,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 966,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 272,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073578,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 283,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 969,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073579,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 970,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 300,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073580,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 970,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 288,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073581,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 299,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 973,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073582,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 974,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 316,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073583,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 974,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 304,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073584,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 315,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 977,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073585,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 978,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 332,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073586,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 978,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 320,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073587,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 331,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 981,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073588,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 982,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 348,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073589,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 982,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 336,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073590,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 347,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 985,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073591,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 986,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 364,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073592,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 986,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 352,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073593,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 363,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 989,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073594,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 990,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 380,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073595,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 990,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 368,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073596,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 379,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 993,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073597,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 994,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 396,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073598,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 994,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 384,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073599,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 395,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 997,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073600,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 998,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 876,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073601,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 998,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 864,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073602,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 875,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 1001,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073603,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 1002,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 892,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073604,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 1002,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 880,
                            slot: 0,
                            pattern: 10,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073605,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 891,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 1005,
                            slot: 0,
                            pattern: 12,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073606,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 1006,
                            slot: 0,
                            pattern: 1,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 908,
                            slot: 0,
                            pattern: 1,
                        },
                    },
                    CompiledPoolV1PairForestLink {
                        tag: 1124073607,
                        weight_kind: 0,
                        weight_level: 0,
                        producer: CompiledPoolV1PairForestEndpoint {
                            row: 1006,
                            slot: 1,
                            pattern: 13,
                        },
                        consumer: CompiledPoolV1PairForestEndpoint {
                            row: 896,
                            slot: 0,
                            pattern: 10,
                        },
                    }];
    }
    #[inline(always)]
    fn lift_m31(value: M31) -> QM31 { QM31::from_cm31(CM31::from_m31(value)) }
    #[inline(always)]
    fn selector_mask_sum_16(values: &[QM31; 16], mut mask: u16) -> QM31 {
        let complement = mask.count_ones() > 8;
        if complement { mask = !mask; }
        let mut sum = if complement { QM31::ONE } else { QM31::ZERO };
        while mask != 0 {
            let index = mask.trailing_zeros() as usize;
            sum =
                if complement {
                    sum.sub(values[index])
                } else { sum.add(values[index]) };
            mask &= mask - 1;
        }
        sum
    }
    pub(crate) struct Selectors {
        pub(crate) high: [QM31; 64],
        pub(crate) low: [QM31; 16],
    }
    #[automatically_derived]
    #[doc(hidden)]
    unsafe impl ::core::clone::TrivialClone for Selectors { }
    #[automatically_derived]
    impl ::core::clone::Clone for Selectors {
        #[inline]
        fn clone(&self) -> Selectors {
            let _: ::core::clone::AssertParamIsClone<[QM31; 64]>;
            let _: ::core::clone::AssertParamIsClone<[QM31; 16]>;
            *self
        }
    }
    #[automatically_derived]
    impl ::core::marker::Copy for Selectors { }
    impl Selectors {
        fn expand<const N :
            usize>(point: &[QM31; 10], start: usize, count: usize)
            -> [QM31; N] {
            let mut weights = [QM31::ZERO; N];
            weights[0] = QM31::ONE;
            let mut len = 1usize;
            let mut coordinate = start;
            while coordinate < start + count {
                let prepared = PreparedQm31Multiplier::new(point[coordinate]);
                let mut index = len;
                while index > 0 {
                    index -= 1;
                    let parent = weights[index];
                    let right = prepared.mul(parent);
                    weights[2 * index] = parent.sub(right);
                    weights[2 * index + 1] = right;
                }
                len *= 2;
                coordinate += 1;
            }
            weights
        }
        pub(crate) fn at_point(point: &[QM31; 10]) -> Self {
            Self {
                high: Self::expand(point, 0, 6),
                low: Self::expand(point, 6, 4),
            }
        }
        #[inline(never)]
        pub(crate) fn boxed_at_point(point: &[QM31; 10]) -> Self {
            Self::at_point(point)
        }
        #[inline(always)]
        pub(crate) fn row(&self, row: usize) -> QM31 {
            if false {
                if !(row < POOL_V1_PAIR_FOREST_COPY_TERMINAL_ROWS_V1) {
                    ::core::panicking::panic("assertion failed: row < POOL_V1_PAIR_FOREST_COPY_TERMINAL_ROWS_V1")
                };
            };
            self.high[row >> 4].mul(self.low[row & 15])
        }
        fn active_literal(&self) -> QM31 {
            let mut sum = QM31::ZERO;
            let mut block = 0usize;
            while block < 64 {
                let mask = constants::ACTIVE_ROW_MASKS[block];
                if mask != 0 {
                    sum =
                        sum.add(self.high[block].mul(selector_mask_sum_16(&self.low,
                                    mask)));
                }
                block += 1;
            }
            sum
        }
        #[inline(always)]
        fn active(&self) -> QM31 { return self.active_literal(); }
    }
    fn pattern_values_literal(openings: &[QM31; POSEIDON2_WIDTH],
        lambda: QM31)
        -> [QM31; POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1] {
        let mut powers = [QM31::ZERO; POSEIDON2_WIDTH];
        let mut power = lambda;
        let mut limb = 0usize;
        while limb < POSEIDON2_WIDTH {
            powers[limb] = power;
            power = power.mul(lambda);
            limb += 1;
        }
        let mut result =
            [QM31::ZERO; POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1];
        let mut pattern_index = 0usize;
        while pattern_index < POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1 {
            let pattern = constants::COPY_PATTERNS[pattern_index];
            let mut value = QM31::ZERO;
            limb = 0;
            while limb < POSEIDON2_WIDTH {
                if pattern.kinds[limb] == 1 {
                    let source =
                        openings[usize::from(pattern.columns[limb])].add(lift_m31(M31(pattern.offsets[limb])));
                    value = value.add(powers[limb].mul(source));
                }
                limb += 1;
            }
            result[pattern_index] = value;
            pattern_index += 1;
        }
        result
    }
    fn pattern_values(openings: &[QM31; POSEIDON2_WIDTH], lambda: QM31)
        -> [QM31; POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1] {
        return pattern_values_literal(openings, lambda);
    }
    struct CopyRowExtension {
        producer_values: [QM31; 2],
        producer_weights: [QM31; 2],
        consumer_values: [QM31; 2],
        consumer_weights: [QM31; 2],
    }
    #[automatically_derived]
    #[doc(hidden)]
    unsafe impl ::core::clone::TrivialClone for CopyRowExtension { }
    #[automatically_derived]
    impl ::core::clone::Clone for CopyRowExtension {
        #[inline]
        fn clone(&self) -> CopyRowExtension {
            let _: ::core::clone::AssertParamIsClone<[QM31; 2]>;
            let _: ::core::clone::AssertParamIsClone<[QM31; 2]>;
            let _: ::core::clone::AssertParamIsClone<[QM31; 2]>;
            let _: ::core::clone::AssertParamIsClone<[QM31; 2]>;
            *self
        }
    }
    #[automatically_derived]
    impl ::core::marker::Copy for CopyRowExtension { }
    fn copy_residual(row: CopyRowExtension, helper: QM31, chi: QM31) -> QM31 {
        let denominators =
            [chi.sub(row.producer_values[0]), chi.sub(row.producer_values[1]),
                    chi.sub(row.consumer_values[0]),
                    chi.sub(row.consumer_values[1])];
        let producer_denominator = denominators[0].mul(denominators[1]);
        let consumer_denominator = denominators[2].mul(denominators[3]);
        let producer_numerator =
            row.producer_weights[0].mul(denominators[1]).add(row.producer_weights[1].mul(denominators[0]));
        let consumer_numerator =
            row.consumer_weights[0].mul(denominators[3]).add(row.consumer_weights[1].mul(denominators[2]));
        producer_denominator.mul(helper.mul(consumer_denominator).add(consumer_numerator)).sub(consumer_denominator.mul(producer_numerator))
    }
    #[inline(always)]
    fn link_weight(link: CompiledPoolV1PairForestLink, append_index: u64,
        variant: PoolV1PairForestCompiledVariantV1) -> M31 {
        match link.weight_kind {
            0 => M31::ONE,
            1 =>
                M31(u32::from(variant ==
                            PoolV1PairForestCompiledVariantV1::PrivateTransfer)),
            2 =>
                M31(u32::from(variant ==
                            PoolV1PairForestCompiledVariantV1::Withdrawal)),
            3 => M31(1 - ((append_index >> link.weight_level) & 1) as u32),
            4 => M31(((append_index >> link.weight_level) & 1) as u32),
            _ => {
                ::core::panicking::panic_fmt(format_args!("internal error: entered unreachable code: {0}",
                        format_args!("generated Pool V1 pair-forest Copy weight")));
            }
        }
    }
    fn accumulate_endpoint(values: &mut [QM31; 2], weights: &mut [QM31; 2],
        endpoint: CompiledPoolV1PairForestEndpoint, tag: u32, weight: M31,
        patterns: &[QM31; POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1],
        selectors: &Selectors) {
        let selector = selectors.row(usize::from(endpoint.row));
        let slot = usize::from(endpoint.slot);
        { weights[slot] = weights[slot].add(selector.mul_m31(weight)); }
        let compressed =
            lift_m31(M31(tag)).add(patterns[usize::from(endpoint.pattern)]);
        values[slot] = values[slot].add(selector.mul(compressed));
    }
    pub(crate) fn evaluate_with_selectors(openings: &[QM31; POSEIDON2_WIDTH],
        h1_z: QM31, selectors: &Selectors, lambda: QM31, chi: QM31,
        append_index: u64, variant: PoolV1PairForestCompiledVariantV1)
        -> PoolV1PairForestCompiledCopyTerminalV1 {
        let patterns = pattern_values(openings, lambda);
        let mut row =
            CopyRowExtension {
                producer_values: [QM31::ZERO; 2],
                producer_weights: [QM31::ZERO; 2],
                consumer_values: [QM31::ZERO; 2],
                consumer_weights: [QM31::ZERO; 2],
            };
        let mut link_index = 0usize;
        while link_index < POOL_V1_PAIR_FOREST_COPY_TERMINAL_LINKS_V1 {
            let link = constants::COPY_LINKS[link_index];
            let weight = link_weight(link, append_index, variant);
            {
                accumulate_endpoint(&mut row.producer_values,
                    &mut row.producer_weights, link.producer, link.tag, weight,
                    &patterns, selectors);
                accumulate_endpoint(&mut row.consumer_values,
                    &mut row.consumer_weights, link.consumer, link.tag, weight,
                    &patterns, selectors);
            }
            link_index += 1;
        }
        let active = selectors.active();
        PoolV1PairForestCompiledCopyTerminalV1 {
            residual: active.mul(copy_residual(row, h1_z, chi)),
            active,
        }
    }
    /// Evaluate the exact 136-link pair-forest Copy lane from the frozen sixteen
    /// merged-C1 openings and one H1 opening. This performs one fixed-size
    /// selector allocation and, under the selected tensor-basis evaluator, one
    /// fixed 103-QM31 scratch allocation. There is no registry- or input-dependent
    /// allocation.
    pub fn evaluate_pool_v1_pair_forest_copy_terminal_compiled_v1(openings:
            &[QM31; POSEIDON2_WIDTH], h1_z: QM31, point: &[QM31; 10],
        lambda: QM31, chi: QM31, append_index: u64,
        variant: PoolV1PairForestCompiledVariantV1)
        -> PoolV1PairForestCompiledCopyTerminalV1 {
        let selectors = Selectors::boxed_at_point(point);
        evaluate_with_selectors(openings, h1_z, &selectors, lambda, chi,
            append_index, variant)
    }
    pub fn pool_v1_pair_forest_copy_active_at_point_compiled_v1(point:
            &[QM31; 10]) -> QM31 {
        Selectors::at_point(point).active()
    }
    /// Source-extraction wrapper for a Boolean terminal row. `variant` is zero
    /// for private transfer and one for withdrawal.
    #[doc(hidden)]
    pub fn pool_v1_pair_forest_copy_lane_boolean_extraction_v1(variant: u8,
        selected_row: u16, openings: &[QM31; POSEIDON2_WIDTH], h1_z: QM31,
        lambda: QM31, chi: QM31, append_index: u64)
        -> Option<PoolV1PairForestCompiledCopyTerminalV1> {
        if usize::from(selected_row) >=
                POOL_V1_PAIR_FOREST_COPY_TERMINAL_ROWS_V1 {
            return None;
        }
        let variant =
            match variant {
                0 => PoolV1PairForestCompiledVariantV1::PrivateTransfer,
                1 => PoolV1PairForestCompiledVariantV1::Withdrawal,
                _ => return None,
            };
        let mut high = [QM31::ZERO; 64];
        let mut low = [QM31::ZERO; 16];
        high[usize::from(selected_row >> 4)] = QM31::ONE;
        low[usize::from(selected_row & 15)] = QM31::ONE;
        let selectors = Selectors { high, low };
        Some(evaluate_with_selectors(openings, h1_z, &selectors, lambda, chi,
                append_index, variant))
    }
    #[inline(always)]
    fn pattern_window(openings: &[QM31; POSEIDON2_WIDTH],
        prepared: [PreparedQm31Multiplier; 8], start: usize) -> QM31 {
        let mut value = QM31::ZERO;
        let mut slot = 0usize;
        while slot < 8 {
            value = value.add(prepared[slot].mul(openings[start + slot]));
            slot += 1;
        }
        value
    }
}
mod host_terminal {
    //! Allocation-bounded selected terminal for the eight-lane Pool V1 pair
    //! forest. The relation keeps the frozen Tag-73 three-opening geometry and
    //! packs Poseidon, 94 semantic source lanes and the 136-link Copy argument
    //! into the same 29 theta lanes as the one-tree payment terminal.
    macro_rules! qm31_array {
        ($n:expr, $index:ident, $body:expr) =>
        {{
                let mut output = [QM31::ZERO; $n]; let mut $index = 0usize;
                while $index < $n { output[$index] = $body; $index += 1; }
                output
            }};
    }
    use crate::host_terminal_field::{qm31_pack_base4, PreparedQm31Multiplier};
    use aspis_core::{
        field::{CM31, M31, QM31},
        state_only_hiding::STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS,
    };
    use aspis_statement::{
        poseidon2::{
            Digest, DIGEST_ELEMS, MERKLE_NODE_COMPRESSION_V3_TWEAK,
            POSEIDON2_WIDTH, RATE,
        },
        state_only_poseidon::{
            evaluate_state_only_poseidon_oracle_projected,
            StateOnlyPoseidonOpenings, StateOnlyPoseidonSelectors,
        },
    };
    use aspis_statement::pool_v1::{
        pair_tree_profile::{
            PoolV1PairLatePublicStatementV1, POOL_V1_PAIR_CAPACITY,
        },
        payment_relation::{
            PoolV1PrivateTransferPublicV1, PoolV1WithdrawalPublicV1,
        },
    };
    use aspis_prover::host_arithmetic::state_only_selected_mask_value;
    use crate::host_copy_terminal::{
        evaluate_with_selectors, PoolV1PairForestCompiledVariantV1, Selectors,
    };
    const DOMAIN_OWNER_KEY: M31 = M31(0x4153_0001);
    const DOMAIN_NULLIFIER: M31 = M31(0x4153_0002);
    const DOMAIN_NOTE: M31 = M31(0x4153_0003);
    pub const POOL_V1_PAIR_FOREST_TERMINAL_ROWS_V1: usize = 1024;
    pub const POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1: usize = 16;
    pub const POOL_V1_PAIR_FOREST_TERMINAL_POINTS_V1: usize = 3;
    pub const POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1: usize =
        POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1 +
                STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS + 2;
    pub const POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1: usize =
        POOL_V1_PAIR_FOREST_TERMINAL_POINTS_V1 *
            POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1;
    pub const POOL_V1_PAIR_FOREST_SOURCE_SEMANTIC_LANES_V1: usize = 94;
    pub const POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1: usize = 24;
    pub const POOL_V1_PAIR_FOREST_POSEIDON_LANES_V1: usize = 4;
    pub const POOL_V1_PAIR_FOREST_COPY_LANES_V1: usize = 1;
    pub const POOL_V1_PAIR_FOREST_THETA_LANES_V1: usize =
        POOL_V1_PAIR_FOREST_POSEIDON_LANES_V1 +
                POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1 +
            POOL_V1_PAIR_FOREST_COPY_LANES_V1;
    pub const POOL_V1_PAIR_FOREST_THETA_COLLISION_DEGREE_V1: usize =
        POOL_V1_PAIR_FOREST_THETA_LANES_V1 - 1;
    pub const POOL_V1_PAIR_FOREST_SEMANTIC_ORACLE_INDIVIDUAL_DEGREE_V1: usize
        =
        26;
    pub const POOL_V1_PAIR_FOREST_SEMANTIC_ZEROCHECK_INDIVIDUAL_DEGREE_V1:
        usize =
        27;
    pub const POOL_V1_PAIR_FOREST_MASKED_TERMINAL_DEGREE_V1: usize = 27;
    pub const POOL_V1_PAIR_FOREST_TERMINAL_FIXED_HEAP_ALLOCATIONS_V1: usize =
        if false { 2 } else { 1 };
    pub const POOL_V1_PAIR_FOREST_TERMINAL_SELECTOR_HEAP_BYTES_V1: usize =
        core::mem::size_of::<Selectors>();
    const SELECTED_H1_COLUMN: usize =
        POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1 +
            STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS;
    const SELECTED_G_COLUMN: usize = SELECTED_H1_COLUMN + 1;
    const VALUE_AUXILIARY_BLOCK: usize = 63;
    const INPUT_OCCUPANCY_ROW: usize = 63 * 16 + 9;
    const OUTPUT_OCCUPANCY_ROW: usize = 63 * 16 + 10;
    const _: () =
        if !(DIGEST_ELEMS == 8) {
            ::core::panicking::panic("assertion failed: DIGEST_ELEMS == 8")
        };
    const _: () =
        if !(POSEIDON2_WIDTH == 16) {
            ::core::panicking::panic("assertion failed: POSEIDON2_WIDTH == 16")
        };
    const _: () =
        if !(POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1 == 28) {
            ::core::panicking::panic("assertion failed: POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1 == 28")
        };
    const _: () =
        if !(POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1 == 84) {
            ::core::panicking::panic("assertion failed: POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1 == 84")
        };
    const _: () =
        if !(POOL_V1_PAIR_FOREST_THETA_LANES_V1 == 29) {
            ::core::panicking::panic("assertion failed: POOL_V1_PAIR_FOREST_THETA_LANES_V1 == 29")
        };
    const _: () =
        if !(POOL_V1_PAIR_FOREST_THETA_COLLISION_DEGREE_V1 == 28) {
            ::core::panicking::panic("assertion failed: POOL_V1_PAIR_FOREST_THETA_COLLISION_DEGREE_V1 == 28")
        };
    mod constants {
        pub const POOL_V1_PAIR_EMPTY_ROOTS_V1: [[u32; 8]; 21] =
            [[1438900896, 782233260, 1544844157, 891350894, 986827501,
                            300047813, 266092546, 1155026732],
                    [141619947, 1448060902, 524379093, 1944458907, 1832113773,
                            579270723, 752346270, 1038346536],
                    [1119858538, 128294437, 939091034, 659145897, 1933666768,
                            903679201, 1182639487, 1398246146],
                    [1057897051, 1132946363, 794377079, 1971564389, 1255722275,
                            926653737, 2031728153, 2024887573],
                    [1410054462, 673771449, 940847521, 274330358, 1719505495,
                            1690439941, 203201419, 1855504616],
                    [1442759752, 1540325866, 188964047, 101815282, 1883549730,
                            1774537487, 1306717763, 561084592],
                    [244193611, 984304317, 1467689208, 2063463197, 1766003332,
                            1300835127, 1578947755, 745931587],
                    [673192756, 38070812, 1453532835, 1340577407, 368420458,
                            1834405704, 270061815, 711700631],
                    [27092219, 1272373356, 998194489, 1458413288, 887470405,
                            1204987730, 864453460, 553704718],
                    [1972918328, 1234090299, 977162835, 1704494754, 1617603773,
                            1819200880, 906453206, 1653526885],
                    [418360492, 472096212, 871749117, 98906847, 2026788776,
                            1504737042, 407274798, 1800828893],
                    [986339640, 660349625, 1012157959, 454024326, 987656904,
                            622864739, 1150440730, 1280042062],
                    [2118470693, 1706590589, 2128512933, 167263577, 409542414,
                            1323179656, 1880070613, 2053396184],
                    [260546973, 1375125357, 1584234519, 1097072342, 1685367984,
                            1070989054, 2113798037, 958210542],
                    [1239966481, 992485427, 1397515674, 466658549, 2071909237,
                            712995354, 2047452742, 1680224983],
                    [1796237568, 1862343136, 1954463912, 1190686266, 364700025,
                            46960257, 671215600, 1214723477],
                    [1127845264, 662862400, 84021756, 995080286, 1419670571,
                            1966281459, 837284626, 2083375353],
                    [1321679286, 782621548, 1415820264, 74436574, 776350425,
                            323154748, 429051705, 1299980413],
                    [1519171444, 1235587172, 1671492368, 1449613582, 547369941,
                            1621086153, 266860322, 450526803],
                    [19381883, 1308966873, 251977766, 474343397, 2069732268,
                            1863820229, 152153379, 665567443],
                    [1201428963, 1296676114, 441891487, 1910121140, 602621674,
                            1294160489, 1878016864, 855887413]];
    }
    pub enum PoolV1PairForestSemanticTerminalErrorV1 {
        InvalidPublicAmount,
        InvalidAppendTransition,
    }
    #[automatically_derived]
    #[doc(hidden)]
    unsafe impl ::core::clone::TrivialClone for
        PoolV1PairForestSemanticTerminalErrorV1 {
    }
    #[automatically_derived]
    impl ::core::clone::Clone for PoolV1PairForestSemanticTerminalErrorV1 {
        #[inline]
        fn clone(&self) -> PoolV1PairForestSemanticTerminalErrorV1 { *self }
    }
    #[automatically_derived]
    impl ::core::marker::Copy for PoolV1PairForestSemanticTerminalErrorV1 { }
    #[automatically_derived]
    impl ::core::fmt::Debug for PoolV1PairForestSemanticTerminalErrorV1 {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            ::core::fmt::Formatter::write_str(f,
                match self {
                    PoolV1PairForestSemanticTerminalErrorV1::InvalidPublicAmount
                        => "InvalidPublicAmount",
                    PoolV1PairForestSemanticTerminalErrorV1::InvalidAppendTransition
                        => "InvalidAppendTransition",
                })
        }
    }
    #[automatically_derived]
    impl ::core::marker::StructuralPartialEq for
        PoolV1PairForestSemanticTerminalErrorV1 {
    }
    #[automatically_derived]
    impl ::core::cmp::PartialEq for PoolV1PairForestSemanticTerminalErrorV1 {
        #[inline]
        fn eq(&self, other: &PoolV1PairForestSemanticTerminalErrorV1)
            -> bool {
            let __self_discr = ::core::intrinsics::discriminant_value(self);
            let __arg1_discr = ::core::intrinsics::discriminant_value(other);
            __self_discr == __arg1_discr
        }
    }
    #[automatically_derived]
    impl ::core::cmp::Eq for PoolV1PairForestSemanticTerminalErrorV1 {
        #[inline]
        #[doc(hidden)]
        #[coverage(off)]
        fn assert_fields_are_eq(&self) {}
    }
    enum CompiledVariant { PrivateTransfer, Withdrawal, }
    #[automatically_derived]
    #[doc(hidden)]
    unsafe impl ::core::clone::TrivialClone for CompiledVariant { }
    #[automatically_derived]
    impl ::core::clone::Clone for CompiledVariant {
        #[inline]
        fn clone(&self) -> CompiledVariant { *self }
    }
    #[automatically_derived]
    impl ::core::marker::Copy for CompiledVariant { }
    #[automatically_derived]
    impl ::core::fmt::Debug for CompiledVariant {
        #[inline]
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            ::core::fmt::Formatter::write_str(f,
                match self {
                    CompiledVariant::PrivateTransfer => "PrivateTransfer",
                    CompiledVariant::Withdrawal => "Withdrawal",
                })
        }
    }
    #[automatically_derived]
    impl ::core::marker::StructuralPartialEq for CompiledVariant { }
    #[automatically_derived]
    impl ::core::cmp::PartialEq for CompiledVariant {
        #[inline]
        fn eq(&self, other: &CompiledVariant) -> bool {
            let __self_discr = ::core::intrinsics::discriminant_value(self);
            let __arg1_discr = ::core::intrinsics::discriminant_value(other);
            __self_discr == __arg1_discr
        }
    }
    #[automatically_derived]
    impl ::core::cmp::Eq for CompiledVariant {
        #[inline]
        #[doc(hidden)]
        #[coverage(off)]
        fn assert_fields_are_eq(&self) {}
    }
    struct SemanticPublic {
        variant: CompiledVariant,
        pool: [u8; 32],
        deployment_domain: [u8; 32],
        anchor: Digest,
        nullifier: Digest,
        asset_id: M31,
        recipient: Option<Digest>,
        change: Digest,
        withdrawal_amount: Option<u32>,
        transition: PoolV1PairLatePublicStatementV1,
    }
    #[automatically_derived]
    #[doc(hidden)]
    unsafe impl ::core::clone::TrivialClone for SemanticPublic { }
    #[automatically_derived]
    impl ::core::clone::Clone for SemanticPublic {
        #[inline]
        fn clone(&self) -> SemanticPublic {
            let _: ::core::clone::AssertParamIsClone<CompiledVariant>;
            let _: ::core::clone::AssertParamIsClone<[u8; 32]>;
            let _: ::core::clone::AssertParamIsClone<[u8; 32]>;
            let _: ::core::clone::AssertParamIsClone<Digest>;
            let _: ::core::clone::AssertParamIsClone<M31>;
            let _: ::core::clone::AssertParamIsClone<Option<Digest>>;
            let _: ::core::clone::AssertParamIsClone<Option<u32>>;
            let _:
                    ::core::clone::AssertParamIsClone<PoolV1PairLatePublicStatementV1>;
            *self
        }
    }
    #[automatically_derived]
    impl ::core::marker::Copy for SemanticPublic { }
    #[inline(always)]
    fn lift_m31(value: M31) -> QM31 { QM31::from_cm31(CM31::from_m31(value)) }
    /// Count only the trailing one bits used by the twenty-level append tree.
    /// The bounded form is equivalent to capping u64::trailing_ones at twenty.
    fn bounded_append_carry(mut index: u64) -> usize {
        let mut carry = 0usize;
        while carry < 20 {
            if index & 1 == 0 { return carry; }
            index >>= 1u32;
            carry += 1;
        }
        carry
    }
    #[inline(always)]
    fn add_preweighted<const N :
        usize>(packed:
            &mut [QM31; POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1],
        start: usize, values: &[QM31; N]) {
        let first = start / 4;
        let last = (start + N - 1) / 4;
        for group in first..=last {
            let lanes: [QM31; 4] =
                {
                    let mut output = [QM31::ZERO; 4];
                    let mut slot = 0usize;
                    while slot < 4 {
                        output[slot] =
                            {
                                let source = 4 * group + slot;
                                if source >= start && source < start + N {
                                    values[source - start]
                                } else { QM31::ZERO }
                            };
                        slot += 1;
                    }
                    output
                };
            packed[group] = packed[group].add(qm31_pack_base4(&lanes));
        }
    }
    #[inline(always)]
    fn sum_high(selectors: &Selectors, ranges: &[core::ops::Range<usize>])
        -> QM31 {
        let mut sum = QM31::ZERO;
        for range in ranges {
            for block in range.clone() {
                sum = sum.add(selectors.high[block]);
            }
        }
        sum
    }
    #[inline(always)]
    fn reconstruct_10(view: &[QM31; 16]) -> QM31 {
        let mut acc = view[9];
        let mut index = 9usize;
        while index > 0 { index -= 1; acc = acc.add(acc).add(view[index]); }
        acc
    }
    #[inline(always)]
    fn empty_root(level: usize) -> Digest {
        let words = constants::POOL_V1_PAIR_EMPTY_ROOTS_V1[level];
        [M31(words[0]), M31(words[1]), M31(words[2]), M31(words[3]),
                M31(words[4]), M31(words[5]), M31(words[6]), M31(words[7])]
    }
    fn validate_transition(public: SemanticPublic)
        -> Result<(), PoolV1PairForestSemanticTerminalErrorV1> {
        let source = public.transition.live_snapshot;
        let after = public.transition.candidate_afterstate;
        if source.pool != public.pool ||
                            source.deployment_domain != public.deployment_domain ||
                        source.sequence != source.next_pair_index ||
                    source.next_pair_index >= POOL_V1_PAIR_CAPACITY ||
                source.next_pair_index.checked_add(1) !=
                    Some(after.next_pair_index) {
            return Err(PoolV1PairForestSemanticTerminalErrorV1::InvalidAppendTransition);
        }
        let index = source.next_pair_index;
        let carry = bounded_append_carry(index);
        for level in 0..20 {
            if level == carry && carry < 20 { continue; }
            let expected =
                if level < carry || ((index >> level) & 1) == 0 {
                    empty_root(level)
                } else { source.frontier[level] };
            if after.next_frontier[level] != expected {
                return Err(PoolV1PairForestSemanticTerminalErrorV1::InvalidAppendTransition);
            }
        }
        Ok(())
    }
    fn poseidon_selectors(selectors: &Selectors)
        -> StateOnlyPoseidonSelectors {
        StateOnlyPoseidonSelectors {
            block: sum_high(selectors, &[0..57]),
            local: selectors.low,
        }
    }
    #[inline(never)]
    fn initial_variant_selectors(variant: CompiledVariant, high27: QM31,
        high28: QM31, high29: QM31) -> (QM31, QM31, QM31, QM31) {
        match variant {
            CompiledVariant::PrivateTransfer =>
                (high27, QM31::ZERO, high27.add(high28), high29),
            CompiledVariant::Withdrawal =>
                (QM31::ZERO, high27.add(high28).add(high29), QM31::ZERO,
                    QM31::ZERO),
        }
    }
    fn semantic_initial_and_absorption(public: SemanticPublic,
        openings: &StateOnlyPoseidonOpenings, selectors: &Selectors)
        -> ([QM31; 16], [QM31; 16]) {
        let nodes = sum_high(selectors, &[4..25, 33..57]);
        let first_common =
            selectors.high[0].add(selectors.high[1]).add(selectors.high[25]).add(selectors.high[30]);
        let (transfer_first, fixed, private_chunk_eight, private_chunk_two) =
            initial_variant_selectors(public.variant, selectors.high[27],
                selectors.high[28], selectors.high[29]);
        let full_initial_selector =
            selectors.low[0].mul(first_common.add(transfer_first).add(fixed));
        let rate_initial_selector = selectors.low[0].mul(nodes);
        let full = PreparedQm31Multiplier::new(full_initial_selector);
        let full_or_rate =
            PreparedQm31Multiplier::new(full_initial_selector.add(rate_initial_selector));
        let mut initial =
            {
                let mut output = [QM31::ZERO; 16];
                let mut lane = 0usize;
                while lane < 16 {
                    output[lane] =
                        {
                            if lane < RATE {
                                full_or_rate.mul(openings.z[lane])
                            } else { full.mul(openings.z[lane]) }
                        };
                    lane += 1;
                }
                output
            };
        let note_first =
            selectors.high[1].add(selectors.high[30]).add(transfer_first);
        let domain =
            selectors.high[0].mul_m31(DOMAIN_OWNER_KEY).add(note_first.mul_m31(DOMAIN_NOTE)).add(selectors.high[25].mul_m31(DOMAIN_NULLIFIER));
        let length =
            selectors.high[0].mul_m31(M31(8)).add(note_first.mul_m31(M31(18))).add(selectors.high[25].mul_m31(M31(16)));
        initial[RATE] = initial[RATE].sub(selectors.low[0].mul(domain));
        initial[RATE + 1] =
            initial[RATE + 1].sub(selectors.low[0].mul(length));
        let mut chunk_eight =
            selectors.high[0].add(selectors.high[1]).add(selectors.high[2]).add(selectors.high[25]).add(selectors.high[26]).add(selectors.high[30]).add(selectors.high[31]);
        let mut chunk_two = selectors.high[3].add(selectors.high[32]);
        chunk_eight = chunk_eight.add(private_chunk_eight);
        chunk_two = chunk_two.add(private_chunk_two);
        let absorption =
            absorption_lanes_literal(selectors.low[12], fixed, chunk_two,
                chunk_eight, nodes, &openings.z);
        (initial, absorption)
    }
    fn absorption_lanes_literal(low: QM31, fixed: QM31, chunk_two: QM31,
        chunk_eight: QM31, nodes: QM31, openings: &[QM31; 16]) -> [QM31; 16] {
        {
            let mut output = [QM31::ZERO; 16];
            let mut lane = 0usize;
            while lane < 16 {
                output[lane] =
                    {
                        let blocks =
                            if lane < 2 {
                                fixed
                            } else if lane < RATE {
                                fixed.add(chunk_two)
                            } else { fixed.add(chunk_two).add(chunk_eight).add(nodes) };
                        low.mul(blocks).mul(openings[lane])
                    };
                lane += 1;
            }
            output
        }
    }
    #[inline(always)]
    fn add_digest_binding(output: &mut [QM31; DIGEST_ELEMS], selector: QM31,
        opened: &[QM31; POSEIDON2_WIDTH], start: usize, expected: &Digest,
        right_tweak: bool) {
        for lane in 0..DIGEST_ELEMS {
            let mut target = expected[lane];
            if right_tweak && lane + 1 == DIGEST_ELEMS {
                target = target.add(MERKLE_NODE_COMPRESSION_V3_TWEAK);
            }
            output[lane] =
                output[lane].add(selector.mul(opened[start +
                                    lane].sub(lift_m31(target))));
        }
    }
    #[inline(never)]
    fn add_schedule_lanes(packed:
            &mut [QM31; POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1],
        public: SemanticPublic, openings: &StateOnlyPoseidonOpenings,
        selectors: &Selectors) {
        let (initial, absorption) =
            semantic_initial_and_absorption(public, openings, selectors);
        add_preweighted(packed, 0, &initial);
        add_preweighted(packed, 16, &absorption);
    }
    #[inline(never)]
    fn add_path_lanes(packed:
            &mut [QM31; POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1],
        openings: &StateOnlyPoseidonOpenings, selectors: &Selectors) {
        let path_selector =
            sum_high(selectors,
                    &[57..63]).mul(selectors.low[1].add(selectors.low[5]).add(selectors.low[9]).add(selectors.low[13]));
        let path = path_lanes_literal(path_selector, openings);
        add_preweighted(packed, 32, &path);
    }
    fn path_lanes_literal(path_selector: QM31,
        openings: &StateOnlyPoseidonOpenings) -> [QM31; 17] {
        let bit = openings.z[0];
        let mut path = [QM31::ZERO; 17];
        path[0] = path_selector.mul(bit.mul(bit.sub(QM31::ONE)));
        for lane in 0..DIGEST_ELEMS {
            let current = openings.z[1 + lane];
            path[1 + lane] =
                path_selector.mul(QM31::ONE.sub(bit)).mul(openings.succ_z[lane].sub(current));
            path[1 + DIGEST_ELEMS + lane] =
                path_selector.mul(bit).mul(openings.succ_z[RATE +
                                lane].sub(current));
        }
        path
    }
    #[inline(never)]
    fn add_value_lanes(packed:
            &mut [QM31; POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1],
        openings: &StateOnlyPoseidonOpenings, selectors: &Selectors) {
        let value_selectors =
            [selectors.row(16 * VALUE_AUXILIARY_BLOCK),
                    selectors.row(16 * VALUE_AUXILIARY_BLOCK + 2),
                    selectors.row(16 * VALUE_AUXILIARY_BLOCK + 4)];
        let range_selector =
            QM31::ZERO.add(value_selectors[0]).add(value_selectors[1]).add(value_selectors[2]);
        let mut range = [QM31::ZERO; 33];
        let mut index = 0usize;
        while index < 10 {
            range[index] = openings.z[index].square().sub(openings.z[index]);
            index += 1;
        }
        index = 0;
        while index < 10 {
            range[10 + index] =
                openings.succ_z[index].square().sub(openings.succ_z[index]);
            index += 1;
        }
        index = 0;
        while index < 10 {
            range[20 + index] =
                openings.xor12_z[index].square().sub(openings.xor12_z[index]);
            index += 1;
        }
        let reconstructed =
            reconstruct_10(&openings.z).add(reconstruct_10(&openings.succ_z).mul_m31(M31(1
                                <<
                                10))).add(reconstruct_10(&openings.xor12_z).mul_m31(M31(1 <<
                            20)));
        range[30] = openings.z[10].sub(reconstructed);
        range[31] = openings.succ_z[10];
        range[32] = openings.xor12_z[10];
        {
            for residual in &mut range {
                *residual = range_selector.mul(*residual);
            }
            add_preweighted(packed, 49, &range);
        }
        let conservation_selector =
            selectors.row(16 * VALUE_AUXILIARY_BLOCK + 6);
        let conservation =
            [conservation_selector.mul(openings.z[0].sub(openings.z[1]).sub(openings.z[2])),
                    conservation_selector.mul(openings.succ_z[0].sub(openings.succ_z[1]))];
        add_preweighted(packed, 82, &conservation);
    }
    #[inline(never)]
    fn variant_expected_output(variant: CompiledVariant) -> M31 {
        match variant {
            CompiledVariant::PrivateTransfer => M31(1),
            CompiledVariant::Withdrawal => M31(0),
        }
    }
    #[inline(never)]
    fn add_occupancy_lanes(packed:
            &mut [QM31; POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1],
        public: SemanticPublic, openings: &StateOnlyPoseidonOpenings,
        selectors: &Selectors) {
        let input_occupancy = selectors.row(INPUT_OCCUPANCY_ROW);
        let output_occupancy = selectors.row(OUTPUT_OCCUPANCY_ROW);
        let expected_output = variant_expected_output(public.variant);
        let occupancy =
            occupancy_lanes_literal(input_occupancy, output_occupancy,
                expected_output, &openings.z);
        add_preweighted(packed, 0, &occupancy);
    }
    fn occupancy_lanes_literal(input_occupancy: QM31, output_occupancy: QM31,
        expected_output: M31, opened: &[QM31; 16]) -> [QM31; 12] {
        let occupied = opened[0];
        let inverse = opened[1];
        let one_minus = QM31::ONE.sub(occupied);
        let mut occupancy = [QM31::ZERO; 12];
        let both = input_occupancy.add(output_occupancy);
        occupancy[0] = both.mul(occupied.mul(occupied.sub(QM31::ONE)));
        occupancy[1] = both.mul(opened[9].mul(inverse).sub(occupied));
        occupancy[2] = both.mul(one_minus.mul(inverse));
        for lane in 0..DIGEST_ELEMS {
            occupancy[3 + lane] = both.mul(one_minus.mul(opened[2 + lane]));
        }
        occupancy[11] =
            input_occupancy.mul(opened[10].mul(one_minus)).add(output_occupancy.mul(occupied.sub(lift_m31(expected_output))));
        occupancy
    }
    #[inline(never)]
    fn public_digest_lanes(public: SemanticPublic,
        openings: &StateOnlyPoseidonOpenings, selectors: &Selectors)
        -> [QM31; DIGEST_ELEMS] {
        let mut digests = [QM31::ZERO; DIGEST_ELEMS];
        add_digest_binding(&mut digests, selectors.row(56 * 16 + 11),
            &openings.z, 0, &public.anchor, false);
        add_digest_binding(&mut digests, selectors.row(26 * 16 + 11),
            &openings.z, 0, &public.nullifier, false);
        if let Some(recipient) = public.recipient {
            add_digest_binding(&mut digests, selectors.row(29 * 16 + 11),
                &openings.z, 0, &recipient, false);
        }
        add_digest_binding(&mut digests, selectors.row(32 * 16 + 11),
            &openings.z, 0, &public.change, false);
        let source = public.transition.live_snapshot;
        let after = public.transition.candidate_afterstate;
        for level in 0..20 {
            let block = 34 + level;
            if ((source.next_pair_index >> level) & 1) == 0 {
                add_digest_binding(&mut digests, selectors.row(block * 16),
                    &openings.z, RATE, &empty_root(level), true);
            } else {
                add_digest_binding(&mut digests,
                    selectors.row(block * 16 + 12), &openings.z, 0,
                    &source.frontier[level], false);
            }
        }
        add_digest_binding(&mut digests, selectors.row(53 * 16 + 11),
            &openings.z, 0, &after.next_root, false);
        let carry = bounded_append_carry(source.next_pair_index);
        if carry < 20 {
            add_digest_binding(&mut digests,
                selectors.row((33 + carry) * 16 + 11), &openings.z, 0,
                &after.next_frontier[carry], false);
        }
        digests
    }
    #[inline(never)]
    fn scalar_lanes(variant: CompiledVariant, withdrawal_amount_present: bool,
        input_asset: QM31, mut output_scalar: QM31,
        private_transfer_term: QM31, withdrawal_term: QM31) -> [QM31; 2] {
        match variant {
            CompiledVariant::PrivateTransfer => {
                output_scalar = output_scalar.add(private_transfer_term);
            }
            CompiledVariant::Withdrawal => {
                if withdrawal_amount_present {
                    output_scalar = output_scalar.add(withdrawal_term);
                }
            }
        }
        [input_asset, output_scalar]
    }
    fn semantic_packed(public: SemanticPublic,
        openings: &StateOnlyPoseidonOpenings, selectors: &Selectors)
        -> [QM31; POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1] {
        let mut packed =
            [QM31::ZERO; POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1];
        add_schedule_lanes(&mut packed, public, openings, selectors);
        add_path_lanes(&mut packed, openings, selectors);
        add_value_lanes(&mut packed, openings, selectors);
        add_occupancy_lanes(&mut packed, public, openings, selectors);
        add_preweighted(&mut packed, 84,
            &public_digest_lanes(public, openings, selectors));
        let asset_difference = openings.z[1].sub(lift_m31(public.asset_id));
        let input_asset = selectors.row(2 * 16 + 12).mul(asset_difference);
        let output_scalar = selectors.row(31 * 16 + 12).mul(asset_difference);
        let private_transfer_term =
            selectors.row(28 * 16 + 12).mul(asset_difference);
        let withdrawal_amount_value = public.withdrawal_amount.unwrap_or(0);
        let withdrawal_term =
            selectors.row(16 * VALUE_AUXILIARY_BLOCK +
                        2).mul(openings.z[10].sub(lift_m31(M31(withdrawal_amount_value))));
        let scalars =
            scalar_lanes(public.variant, public.withdrawal_amount.is_some(),
                input_asset, output_scalar, private_transfer_term,
                withdrawal_term);
        add_preweighted(&mut packed, 92, &scalars);
        packed
    }
    fn selected_claim(claims:
            &[QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1],
        point: usize, column: usize) -> QM31 {
        claims[point * POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1 +
                column]
    }
    #[inline(never)]
    fn copy_variant(variant: CompiledVariant)
        -> PoolV1PairForestCompiledVariantV1 {
        match variant {
            CompiledVariant::PrivateTransfer =>
                PoolV1PairForestCompiledVariantV1::PrivateTransfer,
            CompiledVariant::Withdrawal =>
                PoolV1PairForestCompiledVariantV1::Withdrawal,
        }
    }
    fn equality_value(left: &[QM31; 10], right: &[QM31; 10]) -> QM31 {
        let mut product = equality_factor(left[0], right[0]);
        let mut index = 1usize;
        while index < left.len() {
            product = product.mul(equality_factor(left[index], right[index]));
            index += 1;
        }
        product
    }
    #[allow(clippy::type_complexity)]
    fn composition_parts(public: SemanticPublic,
        claims: &[QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1],
        point: &[QM31; 10], lambda: QM31, chi: QM31, theta: QM31)
        ->
            Result<(QM31, [QM31; 16],
            [QM31; STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS], QM31, QM31, QM31),
            PoolV1PairForestSemanticTerminalErrorV1> {
        let invalid_amount =
            match public.withdrawal_amount {
                None => false,
                Some(amount) => amount == 0 || amount >= (1 << 30u32),
            };
        if invalid_amount {
            return Err(PoolV1PairForestSemanticTerminalErrorV1::InvalidPublicAmount);
        }
        validate_transition(public)?;
        let openings =
            StateOnlyPoseidonOpenings {
                z: {
                    let mut output = [QM31::ZERO; 16];
                    let mut column = 0usize;
                    while column < 16 {
                        output[column] = selected_claim(claims, 0, column);
                        column += 1;
                    }
                    output
                },
                succ_z: {
                    let mut output = [QM31::ZERO; 16];
                    let mut column = 0usize;
                    while column < 16 {
                        output[column] = selected_claim(claims, 1, column);
                        column += 1;
                    }
                    output
                },
                xor12_z: {
                    let mut output = [QM31::ZERO; 16];
                    let mut column = 0usize;
                    while column < 16 {
                        output[column] = selected_claim(claims, 2, column);
                        column += 1;
                    }
                    output
                },
            };
        let mask_only =
            {
                let mut output =
                    [QM31::ZERO; STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS];
                let mut column = 0usize;
                while column < STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS {
                    output[column] =
                        {
                            selected_claim(claims, 0,
                                POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1 + column)
                        };
                    column += 1;
                }
                output
            };
        let selectors = Selectors::boxed_at_point(point);
        let poseidon =
            evaluate_state_only_poseidon_oracle_projected(&openings,
                &poseidon_selectors(&selectors));
        let semantic = semantic_packed(public, &openings, &selectors);
        let h1_z = selected_claim(claims, 0, SELECTED_H1_COLUMN);
        let copy =
            evaluate_with_selectors(&openings.z, h1_z, &selectors, lambda,
                chi, public.transition.live_snapshot.next_pair_index,
                copy_variant(public.variant));
        let prepared_theta = PreparedQm31Multiplier::new(theta);
        let mut composition = copy.residual;
        let mut index = semantic.len();
        while index > 0 {
            index -= 1;
            composition =
                prepared_theta.mul(composition).add(semantic[index]);
        }
        index = poseidon.len();
        while index > 0 {
            index -= 1;
            composition =
                prepared_theta.mul(composition).add(poseidon[index]);
        }
        Ok((composition, openings.z, mask_only,
                selected_claim(claims, 0, SELECTED_G_COLUMN), h1_z,
                copy.active))
    }
    fn terminal_parts(public: SemanticPublic,
        claims: &[QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1],
        point: &[QM31; 10], lambda: QM31, chi: QM31, theta: QM31,
        zerocheck_point: &[QM31; 10], mu: QM31)
        ->
            Result<(QM31, [QM31; 16],
            [QM31; STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS], QM31),
            PoolV1PairForestSemanticTerminalErrorV1> {
        let (composition, c1, mask_only, g, h1_z, copy_active) =
            composition_parts(public, claims, point, lambda, chi, theta)?;
        let original =
            equality_value(zerocheck_point,
                            point).mul(composition).add(mu.mul(h1_z)).add(mu.mul(mu).mul(QM31::ONE.sub(copy_active).mul(h1_z)));
        Ok((original, c1, mask_only, g))
    }
    fn private_public<'a>(public: &PoolV1PrivateTransferPublicV1,
        transition: &'a PoolV1PairLatePublicStatementV1) -> SemanticPublic {
        SemanticPublic {
            variant: CompiledVariant::PrivateTransfer,
            pool: public.pool,
            deployment_domain: public.deployment_domain,
            anchor: public.anchor_root,
            nullifier: public.nullifier,
            asset_id: public.asset_id,
            recipient: Some(public.recipient_commitment),
            change: public.change_commitment,
            withdrawal_amount: None,
            transition: *transition,
        }
    }
    fn withdrawal_public<'a>(public: &PoolV1WithdrawalPublicV1,
        transition: &'a PoolV1PairLatePublicStatementV1) -> SemanticPublic {
        SemanticPublic {
            variant: CompiledVariant::Withdrawal,
            pool: public.pool,
            deployment_domain: public.deployment_domain,
            anchor: public.anchor_root,
            nullifier: public.nullifier,
            asset_id: public.asset_id,
            recipient: None,
            change: public.change_commitment,
            withdrawal_amount: Some(public.amount),
            transition: *transition,
        }
    }
    macro_rules! define_variant_terminal {
        ($composition:ident, $unmasked:ident, $masked:ident, $public_ty:ty,
        $convert:ident) =>
        {
            #[allow(clippy::too_many_arguments)] pub fn
            $composition(public: &$public_ty, transition:
            &PoolV1PairLatePublicStatementV1, claims:
            &[QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1], point:
            &[QM31; 10], lambda: QM31, chi: QM31, theta: QM31,) ->
            Result<QM31, PoolV1PairForestSemanticTerminalErrorV1>
            {
                Ok(composition_parts($convert(public, transition), claims,
                point, lambda, chi, theta,)? .0)
            } #[allow(clippy::too_many_arguments)] pub fn
            $unmasked(public: &$public_ty, transition:
            &PoolV1PairLatePublicStatementV1, claims:
            &[QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1], point:
            &[QM31; 10], lambda: QM31, chi: QM31, theta: QM31,
            zerocheck_point: &[QM31; 10], mu: QM31,) -> Result<QM31,
            PoolV1PairForestSemanticTerminalErrorV1>
            {
                Ok(terminal_parts($convert(public, transition), claims, point,
                lambda, chi, theta, zerocheck_point, mu,)? .0)
            } #[allow(clippy::too_many_arguments)] #[inline(never)] pub fn
            $masked(public: &$public_ty, transition:
            &PoolV1PairLatePublicStatementV1, claims:
            &[QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1], point:
            &[QM31; 10], lambda: QM31, chi: QM31, theta: QM31,
            zerocheck_point: &[QM31; 10], mu: QM31, eta: QM31,) ->
            Result<QM31, PoolV1PairForestSemanticTerminalErrorV1>
            {
                let (original, c1, mask_only, g) =
                terminal_parts($convert(public, transition), claims, point,
                lambda, chi, theta, zerocheck_point, mu,)?;
                Ok(state_only_selected_mask_value(&c1, &mask_only, g,
                point).add(eta.mul(original)))
            }
        };
    }
    #[allow(clippy :: too_many_arguments)]
    pub fn evaluate_pool_v1_pair_forest_private_transfer_selected_constraint_composition_compiled_v1(public:
            &PoolV1PrivateTransferPublicV1,
        transition: &PoolV1PairLatePublicStatementV1,
        claims: &[QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1],
        point: &[QM31; 10], lambda: QM31, chi: QM31, theta: QM31)
        -> Result<QM31, PoolV1PairForestSemanticTerminalErrorV1> {
        Ok(composition_parts(private_public(public, transition), claims,
                        point, lambda, chi, theta)?.0)
    }
    #[allow(clippy :: too_many_arguments)]
    pub fn evaluate_pool_v1_pair_forest_private_transfer_selected_unmasked_terminal_compiled_tag73_v1(public:
            &PoolV1PrivateTransferPublicV1,
        transition: &PoolV1PairLatePublicStatementV1,
        claims: &[QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1],
        point: &[QM31; 10], lambda: QM31, chi: QM31, theta: QM31,
        zerocheck_point: &[QM31; 10], mu: QM31)
        -> Result<QM31, PoolV1PairForestSemanticTerminalErrorV1> {
        Ok(terminal_parts(private_public(public, transition), claims, point,
                        lambda, chi, theta, zerocheck_point, mu)?.0)
    }
    #[allow(clippy :: too_many_arguments)]
    #[inline(never)]
    pub fn evaluate_pool_v1_pair_forest_private_transfer_selected_masked_terminal_compiled_tag73_v1(public:
            &PoolV1PrivateTransferPublicV1,
        transition: &PoolV1PairLatePublicStatementV1,
        claims: &[QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1],
        point: &[QM31; 10], lambda: QM31, chi: QM31, theta: QM31,
        zerocheck_point: &[QM31; 10], mu: QM31, eta: QM31)
        -> Result<QM31, PoolV1PairForestSemanticTerminalErrorV1> {
        let (original, c1, mask_only, g) =
            terminal_parts(private_public(public, transition), claims, point,
                    lambda, chi, theta, zerocheck_point, mu)?;
        Ok(state_only_selected_mask_value(&c1, &mask_only, g,
                    point).add(eta.mul(original)))
    }
    #[allow(clippy :: too_many_arguments)]
    pub fn evaluate_pool_v1_pair_forest_withdrawal_selected_constraint_composition_compiled_v1(public:
            &PoolV1WithdrawalPublicV1,
        transition: &PoolV1PairLatePublicStatementV1,
        claims: &[QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1],
        point: &[QM31; 10], lambda: QM31, chi: QM31, theta: QM31)
        -> Result<QM31, PoolV1PairForestSemanticTerminalErrorV1> {
        Ok(composition_parts(withdrawal_public(public, transition), claims,
                        point, lambda, chi, theta)?.0)
    }
    #[allow(clippy :: too_many_arguments)]
    pub fn evaluate_pool_v1_pair_forest_withdrawal_selected_unmasked_terminal_compiled_tag73_v1(public:
            &PoolV1WithdrawalPublicV1,
        transition: &PoolV1PairLatePublicStatementV1,
        claims: &[QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1],
        point: &[QM31; 10], lambda: QM31, chi: QM31, theta: QM31,
        zerocheck_point: &[QM31; 10], mu: QM31)
        -> Result<QM31, PoolV1PairForestSemanticTerminalErrorV1> {
        Ok(terminal_parts(withdrawal_public(public, transition), claims,
                        point, lambda, chi, theta, zerocheck_point, mu)?.0)
    }
    #[allow(clippy :: too_many_arguments)]
    #[inline(never)]
    pub fn evaluate_pool_v1_pair_forest_withdrawal_selected_masked_terminal_compiled_tag73_v1(public:
            &PoolV1WithdrawalPublicV1,
        transition: &PoolV1PairLatePublicStatementV1,
        claims: &[QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1],
        point: &[QM31; 10], lambda: QM31, chi: QM31, theta: QM31,
        zerocheck_point: &[QM31; 10], mu: QM31, eta: QM31)
        -> Result<QM31, PoolV1PairForestSemanticTerminalErrorV1> {
        let (original, c1, mask_only, g) =
            terminal_parts(withdrawal_public(public, transition), claims,
                    point, lambda, chi, theta, zerocheck_point, mu)?;
        Ok(state_only_selected_mask_value(&c1, &mask_only, g,
                    point).add(eta.mul(original)))
    }
    /// R0's width-29 view of this exact pair-forest terminal. No generic Spend
    /// terminal, legacy transcript or legacy claim stride is selected here.
    pub mod r0 {
        use super::*;
        use alloc::vec::Vec;
        use aspis_core::field::WideExact;
        use aspis_core::state_only_prefix::r0::{
            Challenges, Error, PointClaims,
        };
        pub enum Public<'a> {
            Transfer(&'a PoolV1PrivateTransferPublicV1,
                &'a PoolV1PairLatePublicStatementV1),
            Withdrawal(&'a PoolV1WithdrawalPublicV1,
                &'a PoolV1PairLatePublicStatementV1),
        }
        #[automatically_derived]
        #[doc(hidden)]
        unsafe impl<'a> ::core::clone::TrivialClone for Public<'a> { }
        #[automatically_derived]
        impl<'a> ::core::clone::Clone for Public<'a> {
            #[inline]
            fn clone(&self) -> Public<'a> {
                let _:
                        ::core::clone::AssertParamIsClone<&'a PoolV1PrivateTransferPublicV1>;
                let _:
                        ::core::clone::AssertParamIsClone<&'a PoolV1PairLatePublicStatementV1>;
                let _:
                        ::core::clone::AssertParamIsClone<&'a PoolV1WithdrawalPublicV1>;
                let _:
                        ::core::clone::AssertParamIsClone<&'a PoolV1PairLatePublicStatementV1>;
                *self
            }
        }
        #[automatically_derived]
        impl<'a> ::core::marker::Copy for Public<'a> { }
        impl<'a> Public<'a> {
            fn semantic(self) -> SemanticPublic {
                match self {
                    Self::Transfer(public, transition) =>
                        private_public(public, transition),
                    Self::Withdrawal(public, transition) =>
                        withdrawal_public(public, transition),
                }
            }
            pub fn transition(self) -> &'a PoolV1PairLatePublicStatementV1 {
                match self {
                    Self::Transfer(_, t) | Self::Withdrawal(_, t) => t,
                }
            }
            /// SPEC §9 declaration order. Pool/domain/sequence and source current
            /// root are not fields of R0P.Public and are not silently hashed here.
            /// Existing reject-only public guards remain in the terminal.
            pub fn public_bytes(self) -> Result<Vec<u8>, Error> {
                fn fields(out: &mut Vec<u8>, values: &[M31])
                    -> Result<(), Error> {
                    for value in values {
                        if value.0 >= aspis_core::field::P {
                            return Err(Error::Public);
                        }
                        out.extend_from_slice(&value.0.to_le_bytes());
                    }
                    Ok(())
                }
                fn frontier(out: &mut Vec<u8>, values: &[Digest; 20])
                    -> Result<(), Error> {
                    fields(out, &values[0])?;
                    fields(out, &values[1])?;
                    fields(out, &values[2])?;
                    fields(out, &values[3])?;
                    fields(out, &values[4])?;
                    fields(out, &values[5])?;
                    fields(out, &values[6])?;
                    fields(out, &values[7])?;
                    fields(out, &values[8])?;
                    fields(out, &values[9])?;
                    fields(out, &values[10])?;
                    fields(out, &values[11])?;
                    fields(out, &values[12])?;
                    fields(out, &values[13])?;
                    fields(out, &values[14])?;
                    fields(out, &values[15])?;
                    fields(out, &values[16])?;
                    fields(out, &values[17])?;
                    fields(out, &values[18])?;
                    fields(out, &values[19])?;
                    Ok(())
                }
                let p = self.semantic();
                let mut out = Vec::new();
                out.push(match p.variant {
                        CompiledVariant::PrivateTransfer => 0,
                        CompiledVariant::Withdrawal => 1,
                    });
                fields(&mut out, &p.anchor)?;
                fields(&mut out, &p.nullifier)?;
                fields(&mut out, &[p.asset_id])?;
                out.push(u8::from(p.recipient.is_some()));
                if let Some(value) = p.recipient {
                    fields(&mut out, &value)?;
                }
                fields(&mut out, &p.change)?;
                out.push(u8::from(p.withdrawal_amount.is_some()));
                if let Some(value) = p.withdrawal_amount {
                    fields(&mut out, &[M31(value)])?;
                }
                let source = p.transition.live_snapshot;
                let after = p.transition.candidate_afterstate;
                out.extend_from_slice(&source.next_pair_index.to_le_bytes());
                frontier(&mut out, &source.frontier)?;
                fields(&mut out, &after.next_root)?;
                frontier(&mut out, &after.next_frontier)?;
                Ok(out)
            }
            /// Fast K path. D is deliberately absent from the terminal formula,
            /// but its three claims remain in the width-29 opening statement.
            pub fn terminal_qm31(self, claims: &[[QM31; 29]; 3],
                alpha: &[QM31; 10], c: &Challenges) -> Result<QM31, Error> {
                let mut selected = [QM31::ZERO; 84];
                let mut i = 0usize;
                while i < 84 { selected[i] = claims[i / 28][i % 28]; i += 1; }
                match terminal_parts(self.semantic(), &selected, alpha,
                        c.lambda, c.chi, c.theta, &c.zc, c.mu) {
                    Ok(parts) => Ok(parts.0),
                    Err(_) => Err(Error::Public),
                }
            }
            /// Extend the existing polynomial evaluator to E without narrowing
            /// adversarial E claims. At fixed K coordinates, substituting
            /// c0+t*c1 for every claim gives degree <=25: the Poseidon evaluator
            /// has two consecutive fifth powers (5*5); Copy has four affine
            /// denominators times H1 (degree 5); the other families have degree
            /// <=3. Selectors, theta, mu and equality weights are constants here.
            /// Hence 26 K evaluations determine its value at t=v exactly.
            /// This is polynomial base extension, not a probabilistic identity
            /// test. The honest K path requires only one terminal evaluation.
            pub fn terminal(self, claims: &PointClaims, alpha: &[QM31; 10],
                c: &Challenges) -> Result<WideExact, Error> {
                if claims.iter().flatten().all(|x| x.c1() == QM31::ZERO) {
                    let values = terminal_values(claims, None);
                    return self.terminal_qm31(&values, alpha,
                                c).map(WideExact::from_qm31);
                }
                let mut total = WideExact::ZERO;
                for i in 0..26u32 {
                    let values = terminal_values(claims, Some(M31(i)));
                    let value = self.terminal_qm31(&values, alpha, c)?;
                    let mut numerator = WideExact::ONE;
                    let mut denominator = M31::ONE;
                    for j in 0..26u32 {
                        if i == j { continue; }
                        numerator =
                            numerator.mul(WideExact::V.sub(WideExact::from_qm31(lift_m31(M31(j)))));
                        denominator = denominator.mul(M31(i).sub(M31(j)));
                    }
                    total =
                        total.add(numerator.mul_qm31(value.mul_m31(denominator.inv())));
                }
                Ok(total)
            }
        }
        #[inline(never)]
        fn terminal_values(claims: &PointClaims, t: Option<M31>)
            -> [[QM31; 29]; 3] {
            let mut values = [[QM31::ZERO; 29]; 3];
            for p in 0..3 {
                for l in 0..29 {
                    let x = claims[p][l];
                    values[p][l] =
                        match t {
                            None => x.c0(),
                            Some(t) => x.c0().add(x.c1().mul_m31(t)),
                        };
                }
            }
            values
        }
    }
    #[inline(always)]
    fn equality_factor(a: QM31, b: QM31) -> QM31 {
        let ab = a.mul(b);
        QM31::ONE.sub(a).sub(b).add(ab).add(ab)
    }
}
pub mod host_public {
    //! Prover-local public byte carrier and selected terminal wrapper.
    use alloc::vec::Vec;
    use aspis_core::{
        field::{M31, QM31},
        state_only_prefix::r0::{Challenges, Error},
    };
    use aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public;
    pub struct OwnedPublic {
        pub withdrawal: bool,
        pub anchor: [u32; 8],
        pub nullifier: [u32; 8],
        pub asset_id: u32,
        pub recipient: [u32; 8],
        pub change: [u32; 8],
        pub withdrawal_amount: u32,
        pub next_pair_index: u64,
        pub frontier: [[u32; 8]; 20],
        pub next_root: [u32; 8],
        pub next_frontier: [[u32; 8]; 20],
    }
    #[automatically_derived]
    #[doc(hidden)]
    unsafe impl ::core::clone::TrivialClone for OwnedPublic { }
    #[automatically_derived]
    impl ::core::clone::Clone for OwnedPublic {
        #[inline]
        fn clone(&self) -> OwnedPublic {
            let _: ::core::clone::AssertParamIsClone<bool>;
            let _: ::core::clone::AssertParamIsClone<[u32; 8]>;
            let _: ::core::clone::AssertParamIsClone<[u32; 8]>;
            let _: ::core::clone::AssertParamIsClone<u32>;
            let _: ::core::clone::AssertParamIsClone<[u32; 8]>;
            let _: ::core::clone::AssertParamIsClone<[u32; 8]>;
            let _: ::core::clone::AssertParamIsClone<u64>;
            let _: ::core::clone::AssertParamIsClone<[[u32; 8]; 20]>;
            let _: ::core::clone::AssertParamIsClone<[u32; 8]>;
            let _: ::core::clone::AssertParamIsClone<[[u32; 8]; 20]>;
            *self
        }
    }
    #[automatically_derived]
    impl ::core::marker::Copy for OwnedPublic { }
    #[inline(never)]
    fn canonical(v: u32) -> Option<u32> {
        if v < 2147483647 { Some(v) } else { None }
    }
    #[inline(never)]
    fn field_byte(v: u32, j: usize) -> Result<u8, Error> {
        let v =
            match canonical(v) {
                Some(v) => v,
                None => return Err(Error::Public),
            };
        Ok((v >> (8u32 * (j as u32))) as u8)
    }
    #[inline(never)]
    fn byte_at(p: OwnedPublic, i: usize) -> Result<u8, Error> {
        if i == 0 { return Ok(if p.withdrawal { 1 } else { 0 }); }
        if i < 33 { return field_byte(p.anchor[(i - 1) / 4], (i - 1) % 4); }
        if i < 65 {
            return field_byte(p.nullifier[(i - 33) / 4], (i - 33) % 4);
        }
        if i < 69 { return field_byte(p.asset_id, i - 65); }
        if i == 69 { return Ok(if p.withdrawal { 0 } else { 1 }); }
        let change = if p.withdrawal { 70 } else { 102 };
        if i < change {
            return field_byte(p.recipient[(i - 70) / 4], (i - 70) % 4);
        }
        if i < change + 32 {
            return field_byte(p.change[(i - change) / 4], (i - change) % 4);
        }
        if i == change + 32 { return Ok(if p.withdrawal { 1 } else { 0 }); }
        let index = if p.withdrawal { 107 } else { 135 };
        if i < index {
            return field_byte(p.withdrawal_amount, i - (change + 33));
        }
        if i < index + 8 {
            return Ok((p.next_pair_index >> (8u32 * ((i - index) as u32))) as
                        u8);
        }
        let front = index + 8;
        if i < front + 640 {
            let j = i - front;
            return field_byte(p.frontier[j / 32][(j % 32) / 4], j % 4);
        }
        if i < front + 672 {
            let j = i - front - 640;
            return field_byte(p.next_root[j / 4], j % 4);
        }
        let j = i - front - 672;
        field_byte(p.next_frontier[j / 32][(j % 32) / 4], j % 4)
    }
    pub fn encode_owned(p: OwnedPublic)
        -> Result<([u8; 1455], usize), Error> {
        let n = if p.withdrawal { 1427 } else { 1455 };
        let mut out = [0u8; 1455];
        let mut i = 0usize;
        while i < n { out[i] = byte_at(p, i)?; i += 1; }
        Ok((out, n))
    }
    pub fn project(public: Public<'_>) -> OwnedPublic {
        let (withdrawal, anchor, nullifier, asset_id, recipient, change,
                withdrawal_amount, transition) =
            match public {
                Public::Transfer(p, t) =>
                    (false, p.anchor_root, p.nullifier, p.asset_id,
                        p.recipient_commitment, p.change_commitment, 0, *t),
                Public::Withdrawal(p, t) =>
                    (true, p.anchor_root, p.nullifier, p.asset_id,
                        [M31::ZERO; 8], p.change_commitment, p.amount, *t),
            };
        let mut out =
            OwnedPublic {
                withdrawal,
                anchor: [0; 8],
                nullifier: [0; 8],
                asset_id: asset_id.0,
                recipient: [0; 8],
                change: [0; 8],
                withdrawal_amount,
                next_pair_index: transition.live_snapshot.next_pair_index,
                frontier: [[0; 8]; 20],
                next_root: [0; 8],
                next_frontier: [[0; 8]; 20],
            };
        out.anchor[0] = anchor[0].0;
        out.nullifier[0] = nullifier[0].0;
        out.recipient[0] = recipient[0].0;
        out.change[0] = change[0].0;
        out.next_root[0] = transition.candidate_afterstate.next_root[0].0;
        out.anchor[1] = anchor[1].0;
        out.nullifier[1] = nullifier[1].0;
        out.recipient[1] = recipient[1].0;
        out.change[1] = change[1].0;
        out.next_root[1] = transition.candidate_afterstate.next_root[1].0;
        out.anchor[2] = anchor[2].0;
        out.nullifier[2] = nullifier[2].0;
        out.recipient[2] = recipient[2].0;
        out.change[2] = change[2].0;
        out.next_root[2] = transition.candidate_afterstate.next_root[2].0;
        out.anchor[3] = anchor[3].0;
        out.nullifier[3] = nullifier[3].0;
        out.recipient[3] = recipient[3].0;
        out.change[3] = change[3].0;
        out.next_root[3] = transition.candidate_afterstate.next_root[3].0;
        out.anchor[4] = anchor[4].0;
        out.nullifier[4] = nullifier[4].0;
        out.recipient[4] = recipient[4].0;
        out.change[4] = change[4].0;
        out.next_root[4] = transition.candidate_afterstate.next_root[4].0;
        out.anchor[5] = anchor[5].0;
        out.nullifier[5] = nullifier[5].0;
        out.recipient[5] = recipient[5].0;
        out.change[5] = change[5].0;
        out.next_root[5] = transition.candidate_afterstate.next_root[5].0;
        out.anchor[6] = anchor[6].0;
        out.nullifier[6] = nullifier[6].0;
        out.recipient[6] = recipient[6].0;
        out.change[6] = change[6].0;
        out.next_root[6] = transition.candidate_afterstate.next_root[6].0;
        out.anchor[7] = anchor[7].0;
        out.nullifier[7] = nullifier[7].0;
        out.recipient[7] = recipient[7].0;
        out.change[7] = change[7].0;
        out.next_root[7] = transition.candidate_afterstate.next_root[7].0;
        out = project_frontier_level(out, transition, 0);
        out = project_frontier_level(out, transition, 1);
        out = project_frontier_level(out, transition, 2);
        out = project_frontier_level(out, transition, 3);
        out = project_frontier_level(out, transition, 4);
        out = project_frontier_level(out, transition, 5);
        out = project_frontier_level(out, transition, 6);
        out = project_frontier_level(out, transition, 7);
        out = project_frontier_level(out, transition, 8);
        out = project_frontier_level(out, transition, 9);
        out = project_frontier_level(out, transition, 10);
        out = project_frontier_level(out, transition, 11);
        out = project_frontier_level(out, transition, 12);
        out = project_frontier_level(out, transition, 13);
        out = project_frontier_level(out, transition, 14);
        out = project_frontier_level(out, transition, 15);
        out = project_frontier_level(out, transition, 16);
        out = project_frontier_level(out, transition, 17);
        out = project_frontier_level(out, transition, 18);
        out = project_frontier_level(out, transition, 19);
        out
    }
    pub fn public_bytes(public: Public<'_>)
        -> Result<([u8; 1455], usize), Error> {
        encode_owned(project(public))
    }
    pub fn materialize_public_bytes(public: Public<'_>)
        -> Result<Vec<u8>, Error> {
        let (bytes, len) = public_bytes(public)?;
        Ok(bytes[..len].to_vec())
    }
    pub fn terminal_qm31(public: Public<'_>, claims: &[[QM31; 29]; 3],
        alpha: &[QM31; 10], c: &Challenges) -> Result<QM31, Error> {
        let p =
            match public {
                Public::Transfer(p, t) =>
                    crate::host_terminal::r0::Public::Transfer(p, t),
                Public::Withdrawal(p, t) =>
                    crate::host_terminal::r0::Public::Withdrawal(p, t),
            };
        p.terminal_qm31(claims, alpha, c)
    }
    #[inline(never)]
    fn frontier_word(frontier: &[[M31; 8]; 20], level: usize, i: usize)
        -> u32 {
        frontier[level][i].0
    }
    #[inline(always)]
    fn project_frontier_level(mut out: OwnedPublic,
        transition:
            aspis_statement::pool_v1::pair_tree_profile::PoolV1PairLatePublicStatementV1,
        level: usize) -> OwnedPublic {
        out.frontier[level][0] =
            transition.live_snapshot.frontier[level][0].0;
        out.next_frontier[level][0] =
            transition.candidate_afterstate.next_frontier[level][0].0;
        out.frontier[level][1] =
            transition.live_snapshot.frontier[level][1].0;
        out.next_frontier[level][1] =
            transition.candidate_afterstate.next_frontier[level][1].0;
        out.frontier[level][2] =
            transition.live_snapshot.frontier[level][2].0;
        out.next_frontier[level][2] =
            transition.candidate_afterstate.next_frontier[level][2].0;
        out.frontier[level][3] =
            transition.live_snapshot.frontier[level][3].0;
        out.next_frontier[level][3] =
            transition.candidate_afterstate.next_frontier[level][3].0;
        out.frontier[level][4] =
            transition.live_snapshot.frontier[level][4].0;
        out.next_frontier[level][4] =
            transition.candidate_afterstate.next_frontier[level][4].0;
        out.frontier[level][5] =
            transition.live_snapshot.frontier[level][5].0;
        out.next_frontier[level][5] =
            transition.candidate_afterstate.next_frontier[level][5].0;
        out.frontier[level][6] =
            transition.live_snapshot.frontier[level][6].0;
        out.next_frontier[level][6] =
            transition.candidate_afterstate.next_frontier[level][6].0;
        out.frontier[level][7] =
            transition.live_snapshot.frontier[level][7].0;
        out.next_frontier[level][7] =
            transition.candidate_afterstate.next_frontier[level][7].0;
        out
    }
}
mod host_terminal_field {
    //! Gated terminal arithmetic helpers; same field operation and accumulation order.
    use aspis_core::field::{M31, CM31, QM31, P};
    #[inline(always)]
    fn cm31_mul_r(value: CM31) -> CM31 {
        CM31::new(value.a.double().sub(value.b),
            value.a.add(value.b.double()))
    }
    pub(crate) struct PreparedQm31Multiplier {
        components: [[M31; 3]; 3],
    }
    #[automatically_derived]
    #[doc(hidden)]
    unsafe impl ::core::clone::TrivialClone for PreparedQm31Multiplier { }
    #[automatically_derived]
    impl ::core::clone::Clone for PreparedQm31Multiplier {
        #[inline]
        fn clone(&self) -> PreparedQm31Multiplier {
            let _: ::core::clone::AssertParamIsClone<[[M31; 3]; 3]>;
            *self
        }
    }
    #[automatically_derived]
    impl ::core::marker::Copy for PreparedQm31Multiplier { }
    #[inline(always)]
    fn prepare_component(component: CM31) -> [M31; 3] {
        [component.a, component.b, component.a.add(component.b)]
    }
    #[inline(always)]
    fn prepared_component_mul(left: [M31; 3], right: CM31) -> CM31 {
        let m0 = left[0].mul(right.a);
        let m1 = left[1].mul(right.b);
        let m2 = left[2].mul(right.a.add(right.b));
        CM31 { a: m0.sub(m1), b: m2.sub(m0).sub(m1) }
    }
    impl PreparedQm31Multiplier {
        #[inline(always)]
        pub(crate) fn new(value: QM31) -> Self {
            Self {
                components: [prepare_component(value.c0),
                        prepare_component(value.c1),
                        prepare_component(value.c0.add(value.c1))],
            }
        }
        #[inline(always)]
        pub(crate) fn mul(self, rhs: QM31) -> QM31 {
            let m0 = prepared_component_mul(self.components[0], rhs.c0);
            let m1 = prepared_component_mul(self.components[1], rhs.c1);
            let m2 =
                prepared_component_mul(self.components[2],
                    rhs.c0.add(rhs.c1));
            QM31 { c0: m0.add(cm31_mul_r(m1)), c1: m2.sub(m0).sub(m1) }
        }
    }
    #[inline(always)]
    fn reconstruct_component(channels: [u64; 3]) -> CM31 {
        let m0 = M31::reduce_u64(channels[0]);
        let m1 = M31::reduce_u64(channels[1]);
        let m2 = M31::reduce_u64(channels[2]);
        CM31 { a: m0.sub(m1), b: m2.sub(m0).sub(m1) }
    }
    #[inline(always)]
    fn reconstruct_channels(sums: [[u64; 3]; 3]) -> QM31 {
        let m0 = reconstruct_component(sums[0]);
        let m1 = reconstruct_component(sums[1]);
        let m2 = reconstruct_component(sums[2]);
        QM31 { c0: m0.add(cm31_mul_r(m1)), c1: m2.sub(m0).sub(m1) }
    }
    #[inline(always)]
    fn accumulate_channels(mut sums: [[u64; 3]; 3], left: QM31, right: QM31)
        -> [[u64; 3]; 3] {
        let left_sum = left.c0.add(left.c1);
        let right_sum = right.c0.add(right.c1);
        let a =
            [[left.c0.a, left.c0.b, left.c0.a.add(left.c0.b)],
                    [left.c1.a, left.c1.b, left.c1.a.add(left.c1.b)],
                    [left_sum.a, left_sum.b, left_sum.a.add(left_sum.b)]];
        let b =
            [[right.c0.a, right.c0.b, right.c0.a.add(right.c0.b)],
                    [right.c1.a, right.c1.b, right.c1.a.add(right.c1.b)],
                    [right_sum.a, right_sum.b, right_sum.a.add(right_sum.b)]];
        sums[0][0] += a[0][0].0 as u64 * b[0][0].0 as u64;
        sums[0][1] += a[0][1].0 as u64 * b[0][1].0 as u64;
        sums[0][2] += a[0][2].0 as u64 * b[0][2].0 as u64;
        sums[1][0] += a[1][0].0 as u64 * b[1][0].0 as u64;
        sums[1][1] += a[1][1].0 as u64 * b[1][1].0 as u64;
        sums[1][2] += a[1][2].0 as u64 * b[1][2].0 as u64;
        sums[2][0] += a[2][0].0 as u64 * b[2][0].0 as u64;
        sums[2][1] += a[2][1].0 as u64 * b[2][1].0 as u64;
        sums[2][2] += a[2][2].0 as u64 * b[2][2].0 as u64;
        sums
    }
    #[inline(always)]
    pub(crate) fn qm31_sum_products2(left: [QM31; 2], right: [QM31; 2])
        -> QM31 {
        let sums = [[0u64; 3]; 3];
        let sums = accumulate_channels(sums, left[0], right[0]);
        let sums = accumulate_channels(sums, left[1], right[1]);
        reconstruct_channels(sums)
    }
    #[inline(always)]
    pub(crate) fn qm31_sum_products3(left: [QM31; 3], right: [QM31; 3])
        -> QM31 {
        let sums = [[0u64; 3]; 3];
        let sums = accumulate_channels(sums, left[0], right[0]);
        let sums = accumulate_channels(sums, left[1], right[1]);
        let sums = accumulate_channels(sums, left[2], right[2]);
        reconstruct_channels(sums)
    }
    #[inline(always)]
    pub(crate) fn qm31_sum_products4(left: [QM31; 4], right: [QM31; 4])
        -> QM31 {
        let sums = [[0u64; 3]; 3];
        let sums = accumulate_channels(sums, left[0], right[0]);
        let sums = accumulate_channels(sums, left[1], right[1]);
        let sums = accumulate_channels(sums, left[2], right[2]);
        let sums = accumulate_channels(sums, left[3], right[3]);
        reconstruct_channels(sums)
    }
    #[inline(always)]
    fn terminal_limb(value: M31) -> u64 { u64::from(value.0) }
    #[inline(always)]
    pub(crate) fn qm31_pack_base4(values: &[QM31]) -> QM31 {
        if !(values.len() <= 4) {
            ::core::panicking::panic("assertion failed: values.len() <= 4")
        };
        let mut padded = [QM31::ZERO; 4];
        let mut i = 0usize;
        while i < values.len() { padded[i] = values[i]; i += 1; }
        let [v0, v1, v2, v3] = padded;
        let p = u64::from(P);
        let c0_a =
            terminal_limb(v0.c0.a) + (p - terminal_limb(v1.c0.b)) +
                            2 * terminal_limb(v2.c1.a) + (p - terminal_limb(v2.c1.b)) +
                    (p - terminal_limb(v3.c1.a)) +
                (2 * p - 2 * terminal_limb(v3.c1.b));
        let c0_b =
            terminal_limb(v0.c0.b) + terminal_limb(v1.c0.a) +
                            terminal_limb(v2.c1.a) + 2 * terminal_limb(v2.c1.b) +
                    2 * terminal_limb(v3.c1.a) + (p - terminal_limb(v3.c1.b));
        let c1_a =
            terminal_limb(v0.c1.a) + (p - terminal_limb(v1.c1.b)) +
                    terminal_limb(v2.c0.a) + (p - terminal_limb(v3.c0.b));
        let c1_b =
            terminal_limb(v0.c1.b) + terminal_limb(v1.c1.a) +
                    terminal_limb(v2.c0.b) + terminal_limb(v3.c0.a);
        QM31 {
            c0: CM31::new(M31::reduce_u64(c0_a), M31::reduce_u64(c0_b)),
            c1: CM31::new(M31::reduce_u64(c1_a), M31::reduce_u64(c1_b)),
        }
    }
}
