# Checked terminal row callbacks and field conversion

Seven further focused Lean 4.32 targets pass for the isolated terminal
translation candidate. They prove all four external matrix-row callback
branches at an arbitrary valid limb, and the exact conversion of four raw
limbs into canonical QM31 coordinates. They do not yet prove the complete
matrix layer or terminal verifier.

The [root evidence review](../evidence/terminal-row-callbacks-20261016/root-review.json)
independently checks source snapshots against receipts, compiled output bytes,
raw axiom logs, raw timing logs, and the dependency edges represented in the
two archived bundles. All 15 successful axiom reports contain only
`propext`, `Classical.choice`, and `Quot.sound`. Eighteen failed attempts are
retained separately and are not counted as proof evidence. The generated
extension slice emits no axiom reports; it is counted only as a successful
compile.

## Exact theorem scope

`RawPoseidonExternalAllRows.call_mut_all_lanes_of_array_bounds` takes the
fixed four-by-four U32 input array and a limb index whose value is below four.
It derives all eight successful array reads from these dimensions and proves
the four actual generated callbacks return the specified U64 row formulas,
leaving their captured input and row number unchanged. Earlier intermediate
callback lemmas take read-success equations explicitly; the final wrapper
discharges them. No canonical-field-input premise is needed for these raw
integer formulas.

`RawPoseidonExtensionWords.extension_from_raw_limbs_words` takes only a
fixed array of four U64 words. It proves that the copied generated conversion
succeeds, returns a canonical QM31 value, and places each input word modulo
the M31 prime in its corresponding coordinate. Its array reads are also
derived internally. The release extraction's `reduce_u62` delegates to the
checked total U64 reducer; the source debug assertion is absent from this
pinned extraction. `extension_limbs_words` proves the reverse coordinate
layout of the generated accessor.

The extension slice copies three named declaration blocks byte-for-byte
from translation G, hash
`8a612e11ee96c7a5a909c40bc09ef1f99e4e515b2b129f64059b5c033aa426fb`.
Only imports and namespace framing are supplied. The existing selected-mask
module does not already define those names. The earlier generated callback
slice and pure matrix-row identity are reused unchanged.

## Focused NUC results

All targets exited zero with zero reported process swaps. The host scopes
used `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, and `TasksMax=128`.
The table gives GNU time's wall time and maximum RSS, not total development
time or aggregate host memory. Exact source revisions, hashes, environment,
runner arguments, successful outputs, and failed attempts are archived.

| Target | Wall time | Peak RSS (KiB) | Axiom reports |
|---|---:|---:|---:|
| RawPoseidonExternalRowClosure | 2.01 s | 3,810,792 | 3 |
| RawPoseidonExternalRowReads | 1.86 s | 3,800,920 | 2 |
| RawPoseidonExternalRowLanes | 2.41 s | 3,817,692 | 3 |
| RawPoseidonExternalRowCalls | 2.15 s | 3,813,248 | 3 |
| RawPoseidonExternalAllRows | 1.85 s | 3,803,908 | 1 |
| RawPoseidonExtensionSlice | 1.16 s | 2,597,868 | 0 |
| RawPoseidonExtensionWords | 1.81 s | 3,799,648 | 3 |

The archive preserves the workspace's recorded base revision
`b40d1cfffadbdf967f84cca23ea4e7f1553d564f`; each new source snapshot is pinned
separately. These sources are published on top of `b40ad6372`. No unchanged
full manifest replay was performed.

## Reuse and remaining composition

The proofs reuse the checked scalar-operation adapters, fixed-array indexing
proof, total M31 reducer, QM31 coordinate definitions, and existing matrix
model. A separate historical `WideTower` provenance note reconciles its
source and successful output with the active bridge's object; its historical
receipt does not record a toolchain version, so that old compile is not
represented as a new Lean 4.32 check.

The missing immediate composition is the construction of the raw array and
the enclosing matrix-layer loop. The generated terminal artifact has 18
`core.array.from_fn` calls at widths 4, 10, 16, and 84. Historical models of
that function exist, but no checked source correspondence was found in the
reuse search. An isolated safe local initializer-loop candidate is being
prepared; it has not been adopted, translated, proved, or measured.

The terminal equality-product source loop is a separate next component. The
target is the constraint residual evaluated at the verifier's challenge
point. Executing the complete Poseidon permutation is not a prerequisite for
this source theorem; the existing permutation model is used later when
connecting an extracted valid trace to spend semantics.

Complete terminal/accepted-verifier correspondence, efficient extraction,
privacy, Fiat–Shamir composition, and source/runtime release obligations
remain open. Production Rust and the previously measured artifacts are
unchanged by this proof checkpoint. No new CU or 100-bit security claim is
made.
