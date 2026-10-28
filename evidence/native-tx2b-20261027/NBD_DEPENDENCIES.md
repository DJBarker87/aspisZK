# Named lower-unit dependencies (OPEN until merged)

Read-only `git ls-tree research evidence/native-tx2a-20261027` found no NBC packet when this job inspected research. No NBC result is assumed. These are required statements, not supplied hypotheses silently counted as proofs. Each is a full native/cohort Result association on the SAME input, preserving failure tag, bytes, field order, and panic/error distinction under the pinned library/runtime interpretation.

| Named dependency | Exact required statement/domain | Uses |
|---|---|---|
| NBD_Dep_M31Decode | Every four input bytes: native from_le_bytes returns Some of their little-endian u32 iff that u32<2147483647, otherwise None; emitted decoder agrees. No canonical-input assumption. | U02 canonical digest decoder consumed by U03/U04 |
| NBD_Dep_M31Encode | Every raw Rust M31(u32), including noncanonical representatives: to_le_bytes gives that EXACT raw u32 little-endian; emitted encoder agrees. Do not impose canonicality on first_canonical_byte's domain. | U04 first_canonical_byte; all digest stores |
| NBD_Dep_DigestDecode | Every32-byte array: decode_digest_canonical returns the SAME eight ordered raw limbs iff all<P; first noncanonical limb maps to AtomicStatementError::NonCanonicalDigest; full emitted Result agrees. | ASJA decoder, Pool checkpoint root |
| NBD_Dep_DigestEncode | Every eight-u32 Digest: encode_digest_canonical concatenates its eight exact four-byte little-endian encodings. Validation belongs to callers. | first_canonical_byte; ASJA/live/late/ASF8/ASR8 encoders |
| NBD_Dep_TransferDecode | Every input slice: native private-transfer public decoder and selected cohort agree, including all WrongLength/header/version/kind/digest/reserved/payment errors in source order and all216 accepted bytes. | ASQ8 private-transfer branch |
| NBD_Dep_WithdrawalDecode | Same full216-byte/native-Result statement for withdrawal, including amount and destination fields. | ASQ8 withdrawal branch |
| NBD_Dep_TransferEncode | Every typed transfer public: native encoder and cohort agree on full Result; success writes exact216 bytes. Derive all validators from this SAME input; do not take an independently successful public. | ASF8 validation and encoding |
| NBD_Dep_WithdrawalEncode | Same full Result/216-byte statement on every typed withdrawal public. | ASF8 validation and encoding |
| NBD_Dep_FixedSlice | On each actual fixed range8/32 used by ASJA: native conversion copies identical bytes into array or returns WrongLength iff lengths differ; Aeneas primitive/library transport retains SAME range. | exact, ASJA decoder |

The digest scanner bridges require NONE of these: they compare arbitrary raw u32s, with bounded native indices. U00 runtime/digest emission trust is not needed for those local pure results. No multiplication stub or additional cryptographic assumption is introduced.

If NBC's eventual statement has a narrower domain, each use above remains OPEN until the caller derives that domain; there is no automatic name-based or branch-based reuse.
