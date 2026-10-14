# Unified conditional Fiat–Shamir focused evidence

Source base: `c236efcc23b416e76e5f562d587834d79a6c98c3`.

Eleven targets passed in the pinned NUC workspace. The 22 preserved attempts
include 10 failures, one superseded success, and 11 final successes.
The final combined checkpoint reports 33 axiom audits; final proofs use only
`propext`, `Classical.choice`, `Quot.sound`, or no axioms. Including the
superseded success, successful logs contain 73 audit reports.

This is evidence for the conditional theorem in
[UNIFIED-FIAT-SHAMIR.md](../../UNIFIED-FIAT-SHAMIR.md), with extractor,
classifier, decision, and D1/D2/D3 explicit. It is not an instantiated
100-bit security, efficient knowledge-extraction, source correspondence,
or privacy certificate. The bound retains the oracle-query factor.

| Target / final attempt | Exit | Wall time | Peak RSS (KiB) | Swap |
|---|---:|---:|---:|---:|
| `R1UnifiedCanonicalProver-c` | 0 | 0:01.59 | 3545384 | 0 |
| `R1UnifiedChainDensity-b` | 0 | 0:01.49 | 3551096 | 0 |
| `R1UnifiedDecoder-b` | 0 | 0:01.66 | 3558300 | 0 |
| `R1UnifiedDecoderBound-b` | 0 | 0:01.70 | 3561636 | 0 |
| `R1UnifiedDispatchAddress-a` | 0 | 0:01.46 | 3548792 | 0 |
| `R1UnifiedDispatchCase-a` | 0 | 0:01.63 | 3560600 | 0 |
| `R1UnifiedFiatShamir-b` | 0 | 0:01.53 | 3551780 | 0 |
| `R1UnifiedFiatShamirCheckpoint-a` | 0 | 0:01.43 | 3536428 | 0 |
| `R1UnifiedInj-a` | 0 | 0:01.47 | 3547244 | 0 |
| `R1UnifiedPayloadZero-d` | 0 | 0:01.67 | 3547636 | 0 |
| `R1UnifiedTotalCase-c` | 0 | 0:01.53 | 3555192 | 0 |

Every compilation used `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`,
`TasksMax=128`, and Lean's 5,000 MiB threshold. The runner checks the aggregate
reservation against a 50 GiB limit before starting each job. The pinned Lean
4.32.0 executable reports revision `8c9756b28d64dab099da31a4c09229a9e6a2ef35`.
This is focused compilation with the pinned dependency cache, followed by one
combined import/axiom checkpoint, not a clean whole-package release replay.

`source-manifest.json` identifies every attempt snapshot, source hash, receipt,
resource log, final source, and object. Two worker snapshots were restored from
local copies after exact NUC receipt/sidecar hash matches. The deterministic
object archive is `objects/unified-fiat-shamir-objects.tar.gz`, SHA-256
`a6fd0b8f95b5c569d18fc48c05debb543dce5364f2fa3d634484cd0c278c28f3`.
There are no loose `.olean` files in this bundle.

`ROOT-VALIDATION.json` records the independent source/evidence audit. Root
inspected the final theorem premises and composition, checked the dependent
checkpoint, verified all attempt/resource/source/object hashes, and confirmed
all 14 central runtime fingerprints remain unchanged. The compile runner and
pinned environment snapshots are in `runner/`; `SHA256SUMS` seals all bundle
files except itself. No new axioms or admitted proofs occur in final sources.
Failed compilation logs are preserved as failed attempts and may contain the
elaborator's `sorryAx` diagnostic; they are never counted as successful proofs.
