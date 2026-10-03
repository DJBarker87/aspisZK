# R481: lossless packed QM31 cell representation

`R481NativeQM31Cell.lean` compiled successfully on pinned Lean 4.32 from revision
`b9ccc3356b15e1fbb459d7dfd4353dab96a3220a`. Exit 0; wall time 1.55 seconds;
peak Lean RSS 3,717,120 KiB; swaps 0. The exact source SHA256 is
`77fb6fd0d5e0e55c085541be65181f8ba3ca6905cd3daa33cef32c5e4c56efbd`.

The theorem gives a bijection between the generated source `field.QM31` value
and a 128-bit cell containing four 32-bit lanes. It proves all four lane reads
and both encode/decode inverses. The proofs are universal over **all source
word values and all 128-bit cells**, without canonical-field premises. Thus
noncanonical bit patterns remain represented exactly; no normalization,
truncation, or negative-input filtering is introduced.

The inspected R440 host capture records: QM31 type2, size16/align4, c0/c1
offsets0/8; CM31 type30, size8/align4, a/b offsets0/4; M31 type47,
size4/align4, inner u32 offset0. The captured target is x86_64 little endian
with 8-byte pointers. This gives the associated four byte offsets0/4/8/12.
Exact metadata rows and graph checksum are retained. This association is not a
kernel-certified metadata decoder, proof of native compiler ABI semantics,
or evidence of the SBF artifact's layout.

All fourteen complete `#print axioms` reports contain only `propext`,
`Classical.choice`, `Quot.sound`, or no axioms. They contain no `sorryAx`.
The 128-bit identities use symbolic `bv_decide` proofs, not concrete recurrence
normalization. Exact source, receipt, logs, complete reports, runner, layout
association and superseded failed/intermediate attempts are in
[evidence/r481-native-qm31-cell](evidence/r481-native-qm31-cell/).
The final successful source was not recompiled after promotion. Existing
16-byte transcript serialization results were not replayed.

The capped job used `lake env lean -j1 -M4500`, `MemoryHigh=5G`,
`MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`. RSS measures the Lean child.

## First remaining proposition

Bind the selected native raw-pointer dereference to the initialized cell
representation and actual caller reference, deriving memory-image, permissions,
lifetime and frame conditions. R481 proves a representation prerequisite,
not allocation initialization or a native read. R480's explicit
`a.cells = v.val` premise remains unproved for native execution. The existing
Aeneas backend still rejects raw dereference; a source-preserving memory
bridge is required before the actual Fun70 fold and callback chronology can
be claimed.

No privacy, soundness or end-to-end security gate is closed by this result.
Universal joint mask compatibility, whole-view simulation and shared-oracle
losses, and original quotient extraction/source-acceptance soundness remain
required. Verifier source, parameters, and 999,790 / 999,532 CU results remain
unchanged. No CU benchmark or unchanged regression was rerun.
