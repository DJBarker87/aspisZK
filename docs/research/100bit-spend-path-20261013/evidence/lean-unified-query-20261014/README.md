# Unified query-decoder focused evidence

Source base: `ff314073cab76662de4e5711cdda5542c8bcfb62`.

Fourteen targets passed in the pinned NUC workspace. The 38 preserved attempts
include 23 failures, one superseded green attempt, and 14 final successes.
The final combined checkpoint reports 39 axiom audits; final proofs use only
`propext`, `Classical.choice`, `Quot.sound`, or no axioms. Including the
superseded success, successful logs contain 82 audit reports.

This is evidence for the component statements in
[UNIFIED-QUERY-DECODER.md](../../UNIFIED-QUERY-DECODER.md), not an end-to-end
soundness, source correspondence, or privacy certificate. The completing-law
bound keeps its fixed-prefix premise explicit.

| Target / final attempt | Exit | Wall time | Peak RSS (KiB) | Swap |
|---|---:|---:|---:|---:|
| `R1BackgroundOwnMap-b` | 0 | 0:00.91 | 1811672 | 0 |
| `R1DecoderStateList-c` | 0 | 0:00.83 | 1807232 | 0 |
| `R1PrefixQueryTrace-c` | 0 | 0:01.56 | 3545400 | 0 |
| `R1PublicInitAbsorbSeparation-c` | 0 | 0:00.90 | 1811424 | 0 |
| `R1QueryBackgroundChain-b` | 0 | 0:01.61 | 3547544 | 0 |
| `R1QueryBackgroundLaw-b` | 0 | 0:01.47 | 3537516 | 0 |
| `R1QueryChainTraceFacts-e` | 0 | 0:01.72 | 3545652 | 0 |
| `R1UnifiedLabels-a` | 0 | 0:00.79 | 1808372 | 0 |
| `R1UnifiedQueryCase-a` | 0 | 0:01.54 | 3553116 | 0 |
| `R1UnifiedQueryCheckpoint-a` | 0 | 0:01.40 | 3530000 | 0 |
| `R1UnifiedQueryDecoder-a` | 0 | 0:01.56 | 3552596 | 0 |
| `R1UnifiedQueryInjection-h` | 0 | 0:01.63 | 3553800 | 0 |
| `R1UnifiedQueryLaw-d` | 0 | 0:01.53 | 3550524 | 0 |
| `R1UnifiedQueryView-b` | 0 | 0:01.57 | 3550276 | 0 |

Every compilation used `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`,
`TasksMax=128`, and Lean's 5,000 MiB threshold. The runner checks the aggregate
reservation against a 50 GiB limit before starting each job. The pinned Lean
4.32.0 executable reports revision `8c9756b28d64dab099da31a4c09229a9e6a2ef35`.

`source-manifest.json` identifies every attempt snapshot, source hash, receipt,
resource log, final source, and object. Some worker snapshots were retained
locally; each copied snapshot was checked against the NUC receipt and hash
sidecar. The deterministic object archive is
`objects/unified-query-objects.tar.gz`, SHA-256
`516238e9b8c17503438009041e8271d6283ed4e987b76a93f94d08c6eb6e96ac`.
There are no loose `.olean` files in this bundle.

`ROOT-VALIDATION.json` records the independent source/evidence audit. Root
inspected theorem premises and proof routes, checked the new dependent
checkpoint, verified all attempt/resource/source/object hashes, and confirmed
all 14 central runtime fingerprints remain unchanged. The compile runner and
pinned environment snapshots are in `runner/`; `SHA256SUMS` seals all bundle
files except itself.
