# Selected packed records to the typed query residual

Status: **kernel checked** for the scoped observed-record algebra. The focused
target is `experiments/SelectedPackedQueryBridgeV3.lean`, SHA256
`71d263e01f07515e094b98cc7a21734d73137be7da9e6a2dbd6d655393f9f954`,
with ten audit declarations (including the new generic congruence helper). Source parent is
`8761cd89ab7ccea779ef4a9f86fa415d670bd16d`; the inherited NUC runner's
creation parent remains `289d7356c78a4cd493fe61a54f9548f2a0c11298`.
The coordinator ran four focused attempts: three failures followed by green
V3. All four exact source/log/manifest triplets are retained locally, and the
green output was copied and hash-verified. No unchanged Lean replay was run.

| Exact tag | Target | Exit | Wall seconds | Peak RSS KiB | Swaps |
|---|---|---:|---:|---:|---:|
| selected-packed-query-bridge-nuc-v1 | SelectedPackedQueryBridge | 1 | 0.08 | 184636 | 0 |
| selected-packed-query-bridge-nuc-v2 | SelectedPackedQueryBridge | 1 | 3.28 | 6808020 | 0 |
| selected-packed-query-bridge-v2-nuc-v1 | SelectedPackedQueryBridgeV2 | 1 | 3.65 | 6809448 | 0 |
| selected-packed-query-bridge-v3-nuc-v1 | SelectedPackedQueryBridgeV3 | 0 | 4.81 | 6844452 | 0 |

V3's ten exact audits use only `propext`, `Classical.choice`, and `Quot.sound`;
the generic `expanded_congr` uses only `propext` and `Quot.sound`. Its final
log contains no errors, warnings or `sorryAx`. Source maxRecDepth200 and
maxHeartbeats200000 remain unchanged. The successful command used Lean
4.32.0 commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`, `-j1 -M9500`,
MemoryHigh8GiB/MemoryMax10GiB/MemorySwapMax0/CPU200%. Measurements describe
the focused Lean child, not prover/verifier runtime. Exact green hashes:

- Source/snapshot: `71d263e01f07515e094b98cc7a21734d73137be7da9e6a2dbd6d655393f9f954`.
- Olean: `84fe18f47a8b6a667ff54d5c30588ef59fa73facb91c8cc81213c5186814f6e0`.
- Log: `ea59d5a0c8432d5e4e1665f6b864256e3cf8727969ec3433de7c5efc4bfe6954`.
- Attempt manifest: `d57d98dfdea0fadd9bb4dd97d9e668bcf1b359942aa074fba28c81cbcaa9992a`.

The first attempt stopped on missing cached dependencies. After restoring the
14 exact dependency pairs, the second reached the proof and exited 1 in
3.28 seconds, with 6,808,020 KiB peak RSS and zero swaps. Its only primary
errors were an unresolved `slotIndex` dimension and the now-reserved binder
token `matches`; later errors cascaded. Fresh V2 supplies `n:=262144` and
renames the binder to `matchAt`, with no mathematical or resource change.
The initial source SHA256 remains
`08019de6ae9620d9f05c4d539bd3e3e0ac5bbd26af885245466c7336adf9421b`.

V2 reached all declarations but `matching_fold` exceeded recursion depth 200
while elaborating a `congrArg` over the fully concrete fold. It exited 1 in
3.65 seconds, with 6,809,448 KiB peak RSS and zero swaps. Its immutable source
hash is `cd5a98314c0af84c6018fe18d219cda2b0a8311c86345c6781235b1594260f17`.
V3 adds the small generic ring theorem `expanded_congr` and applies it to
explicit scalar/slot arguments after unfolding only the two outer fold
definitions. The selected theorem statement and recursion/memory caps are
unchanged; failed dependent audits are not credited as certificates.

## Exact boundary and existing proof reuse

The active source is `relation_callback.rs::opened_values_prepared` followed
by `inject`. The callback SHA256 remains
`285c90695cc7558a88ffc7cb50de4235b68c7ceed9d0600d5cc9ba7f682607ed`;
the inspected `query_arithmetic.rs` SHA256 is
`57590907abf1c6a278cca0babc49b4c916a87a0a44e1f265b9bea28cc9fd52b1`.
The callback was previously pinned to executed source checkpoint
`9e432896a4e1515efebe940b71fd9b4f9f009189`; this task performs no runtime
build or new executed-binary claim.

| Source boundary | Exact model or new interface |
|---|---|
| Complete-body record ordinal i | Existing `PackedQueryRecord.bodyRecord`, offset `11228+621*i`; `bodyRecord_byte_exact` removes fallback under `CanonicalRelationInput.parseFixed` success |
| C1 bytes 0..402 | 104 canonical 31-bit limbs, `26*slot+column` |
| C2 bytes 403..588 | 48 canonical 31-bit limbs, `4*(4*helper+slot)+basis`; tower order `c0.re,c0.im,c1.re,c1.im` |
| Salt bytes 589..620 | 32 bytes, no field interpretation; not part of gamma arithmetic |
| Gamma combination | Existing `combined_eq_raw`: base lanes 0..25, then H/G/D at powers 26/27/28 |
| Affine subtraction | New `recordSlots`: combined minus `intercept+slope*(useX ? x : y)` |
| Chord denominator | Existing `sourceDenom_eq`: `a+b*x+c*y`, signs `(++,+−,−−,−+)` |
| Checked division | Existing `SelectedQueryBuffer.inverse_eq` and `QueriedResidual.success_slots`; flat slot index `4*ordinal+slot` |
| Fold inverses | Existing inverse constructor: indices `2*ordinal` and `2*ordinal+1` for `2*x,2*y` |
| Alpha0 fold | New `matching_fold` transports four scalar slots into existing `QueriedResidual.success_fold`; negative-y pair and cubic-alpha signs retained |
| Typed received value | New `observed_fold`, at the same `storedPoint(query[i]) = 2*x²−1` |
| Query residual | New `observed_residual`: exact final256 evaluation **minus** normalized received fold |
| Shifted batch | New `q22_received_sum`: `rho^(ordinal+1)`, in original record order, not sorted authentication order |
| Zero denominator | New `source_pole_reject`: returns `none`; total division at zero is never treated as accepted arithmetic |

The mathematical parser and canonical raw-limb identities are already green
in `PackedQueryRecord`; they are not re-proved here. The ordered inverse and
fold implementation interface is already green in `SelectedQueryBuffer` and
`QueriedResidual`. `TupleQueryTransport` concerns tuple/source zero checks
and would add no needed record-parser theorem, so it is not imported.

## Precise result and causality restriction

For distinct queried indices, `observedWord` is a deterministic extension of
the raw gamma-combined record values at those indices, with zero elsewhere.
Its slot equalities are derived by the generic `extendRows_at`, not supplied
as unexplained equations. Parser success plus checked inverse success then
derive the observed quotient, received fold, and residual for that SAME word.
A single record is the special case `q=1`; `q22_received_sum` handles the
complete ordinal family without reordering or an independence premise.

This extension is deliberately **post-query**. It may depend on gamma,
alpha, the query indices, every supplied record, and an adaptive final256.
Its existence does not construct the fixed pre-gamma/pre-alpha oracle required
by a causal probability theorem. Distinctness is an explicit input to the
extension; this leaf proves neither a fresh query schedule nor the executable
query sampler's distinctness. Repeated indices with conflicting record values
cannot be extended to one word. The lower-level `matching_slots` and
`matching_fold` allow repetitions if a caller separately proves consistency
with an external word.

For composition with `TypedRelationTerminalV3`, `observed_fold` identifies its
mathematical `received` values and `observed_residual` identifies
`PostQueryFunctional.residual`. The q22 sum supplies the same shifted query
contribution to the carried claim. The terminal theorem keeps an arbitrary
ordinary/image prior, so there is no assumption that the pre-query discrepancy
was already zero. No restriction `alpha0 != 0` is added. No new acceptance,
authentication, freshness, probability, or extraction conclusion follows.

## Why this differs from the old failed draft

The old `PackedQueryResidual` v1–v9 attempt history remains immutable and
unclaimed. Its final failure eliminated equality between concrete inverses,
unfolding nested QM31 norms and M31 modular arithmetic. This leaf never needs
that equality elimination. It uses exactly the same checked inverse array on
both sides of `matching_slots`, then applies the generic `expanded_congr`
theorem to four abstract slots.
Existing checked theorems do the inverse-to-oracle transport. No option,
memory cap, theorem assumption, or frozen dependency is changed to repair
the old elaboration failure.

## Tiny exact falsification control

`python3 experiments/check_selected_query_record.py` exited 0 in 0.037 seconds
(command wall observation; no RSS or swap measurement was taken). Output is
retained as `experiments/selected-query-record-control.json`. This is a tiny
Python arithmetic control, not an optimized Rust release gate or a Lean proof.

It tests all 4,712 single-bit positions of the 104+48 limbs against the literal
31-bit model and the selected four-load/shift/OR decoder, plus all 152
placements of the forbidden M31 value `2^31−1`. The 621-byte labelled fixture
has SHA256 `a9241bf58983fbdb77425fcca61b473dc90459f984d8e99007d796626f871524`.
The script reconstructs it exactly; a separate binary file is unnecessary.

Wrong C1 indexing gives 10 instead of 29; wrong C2 helper/slot ordering gives
1032 instead of 1028. Swapping slots 2/3 changes the fold. Sorting two arithmetic
records changes the shifted-rho sum from 26 to 22. The residual-sign control
gives discrepancy −82 on both correct formulas. Alpha zero reduces to the
four-slot average. A queried zero denominator is identified as rejection.
The rational fold test is a generic scalar-sign control, not a claim that its
chosen coordinates belong to the selected stored circle domain. The gamma
control uses prime-subfield tower values; arbitrary tower multiplication is
handled only by existing formal arithmetic, not this finite test.

The basis tests are useful falsifiers, not by themselves a formal proof of
optimized word operations for all bytes. The complete optimized decoder,
delayed reductions, prepared tower multiplication, point lookup and compiled
Rust buffer path still require their exact machine/source composition.

## Dependency provenance and reproducible metadata audit

`experiments/selected-packed-query-dependency-preflight.json` records a
read-only comparison with the retained TypedRelationTerminalV3 manifest
SHA256 `00d86bf0569a13d89f32d198b3689acd41b4be9dd89f67d107d2caa7eeb07c2d`.
Fourteen research source/olean pairs are absent from that manifest:
PackedQueryRecord, PackedLimbCollect, CanonicalCollect, CanonicalRelationInput,
SelectedQueryBuffer, LineNormBuffer, QueriedInverse, JoinedInverse, CircleNorm,
ChordNorm, LineNorm, SharedInverseReplay, QueriedResidual, QuotientFold.
Every local pair matches a retained green dependency receipt. The four
non-Mathlib import boundaries (V7PackedFibreDecoder, OptimizedRelationRefinement,
V5ComponentCQM31TowerExact, SelectedQuotientOriginal) match BOTH source and
olean bytes in the current retained manifest: eight exact boundary matches,
no observed variant. This audit stops at those registered boundaries and
does not independently re-certify their full transitive closure.

These are old Lean 4.32.0/Mathlib81a5 receipts, with borrowed sources pinned
at `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`. They were compiled on arm64
macOS; the green target now observes successful native NUC import, not a
complete cross-platform build certificate. CanonicalCollect
and CanonicalRelationInput were previously restored remotely but omitted
from the 1053-entry manifest; that omission is preserved, not retroactively
repaired in old evidence.

All 14 pairs are installed but omitted from all four actual run manifests.
Each log checks 1059 registered entries; only the successful log checks them
again after compilation. This is not a complete imported-closure certificate.
The original preflight JSON remains the historical pre-install observation.
`experiments/selected-packed-query-restored-dependencies.txt` records a
separate read-only observation at **2026-09-11T12:17:55Z**, reached through
Tailscale `dombarker@100.108.41.90`. Its 28 hashes match the old green receipts
and the present local pairs. Observation SHA256:
`2165cca6ab739534c3cc0467922ca43dbdf6b0d77da7cb7dfeaa6dbdcdb784ac`.
These are explicitly post-run hashes, not checksums taken during execution
or an original cache-copy receipt. No old manifest was rewritten.

The clone-portable, read-only auditor checks all four attempt snapshots,
sources, logs, caps, axiom declarations, the 14 omitted dependency pairs,
eight registered boundary hashes, and retained control/report bytes. Oleans
are optional in a publication clone but must match exactly whenever present.
It performs no SSH, compilation, or file writes:

```sh
python3 docs/research/v8-no-work-100-20260907/experiments/audit_selected_packed_query_bridge.py --check-recorded
git diff --check
```

Expected result: one green target, ten standard audits, four exact attempts,
three failures; restoration omissions explicit. The separate machine-readable
record is `experiments/selected-packed-query-bridge-evidence.json`.
