# Current native field decoder and universal successful-output canonicality

`S9NativeWideDecoderRecordMapV1` proves a FULL Result map from the CURRENT transparent native WideExact byte decoder to the existing checked RecordParser decoder, through the existing owned decoder maps. This preserves the length guard, all32 ordered source byte reads, strict limb checks, successful values, None, failure and divergence. Only nominal record carriers are copied. Existing parser/byte arithmetic is reused.

`S9NativeFieldActualCanonicalV1` derives actual start/next/finish wrapping offsets, selected source window and decoderSome from the SAME accepted actual weights.field(bytes,i) call. It then reuses the checked decoder/ReaderE canonicality proof to establish all eight limb bounds and the EXISTING native WideExact canonicality predicate. It also derives selected length32 and successful source reads at every byte index below32. No input/dataCan, decoderCorrectness, externally supplied selected slice or child decoder success is assumed.

Canonicality holds for EVERY successful actual field call, including large wrapping-index aliases. This must not be confused with equality of complete field readers: actual weights.field uses WRAPPING offset arithmetic, while existing S5 readerBody uses CHECKED arithmetic.

The arithmetic-only counterexample script records a64-bit i=2^59 alias: current wrapping offsets select[0,32), whereas checked i*32 overflows. On a canonical32-zero-byte input the transparent source decoder has the same zero field case; unrestricted complete-reader equality cannot be claimed. This packet does not claim a formally executed full-reader counterexample or a checked-reader join. A separate bounded-index proof is required at actual callers (S2/two-fold Pair supplies n=64, and regular dot indices<n).

Validation: two smallest changed targets,13.050s/21.771s, standard-only axiom reports, zero swap. Existing owned/RecordParser/ReaderE proofs and sourceScalar maps are reused without reruns. Exact current qualified source371afe… and dependency/profile/toolchain pins are included. No binaries, source-body replacement, cold dependency build or full release-manifest replay is included.

Checked S5 reader correspondence, actual caller index-domain discharge, complete Rust/runtime/artifact binding, full Pair value semantics, privacy and100-bit security remain outside this closure.
