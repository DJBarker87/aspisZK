# R493 slice-length builtin alias build

This archive preserves the exact narrow `ExtractBuiltinLean` source patch and
the successful Aeneas-tool build record. The patch recognizes the
monomorphized slice-length source name using the existing `Slice.len` builtin;
the unchanged non-monomorphized registration remains in the archived source.

The build record pins source revision
`56a931fc3879354a2fa584e73bd0a1d412714851` and launch revision
`078a3bd7d4471a5f10549843e7818b956163bb77`. It records exit 0, wall time
1:23.56, peak RSS 566,100 KiB, zero swap, and candidate binary SHA-256
`c8562f6354832214639c5325ca0cc586ada9671189395c19a6fd6f37a7bdabee`
(49,496,368 bytes). The binary is retained at the source evidence path named
in `build/build-result.json`; its hash and size are recorded there instead of
duplicating it in this archive.

No translation or Lean compilation was run. This build evidence is not a
formal proof.
