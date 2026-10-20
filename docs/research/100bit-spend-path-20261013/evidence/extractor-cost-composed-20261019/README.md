# Extractor cost composition packet

Schema: `focused-extractor-proof-packet-v1`.
Status: **checked conditional composition; implementation obligations remain open**.

The consumer theorem is
`AspisR1.RawExtractorCostComposedV2.recorded_extractor_cost_and_failure`
(`lean/RawExtractorCostComposedV2.lean:124`). For accepted runs of the exact
compiled experiment used by `checked_acceptance_failure_bound_no_model`, it
bounds the uniform private-coin mean of field operations, recorded-log reads
and bits by the explicit polynomial `Parameters.attemptBudget`. It also
proves returned-witness validity and preserves the failure ledger
`kappa Q + N*B + 2^-126`, with `2^-126 ≤ 2^-120`.

This is conditional on output refinement, bounded arithmetic occurrence lists,
implementation overhead, executable log reconstruction and bit accounting.
Uniform overhead constants/degree must be fixed across an input family.
See `../../design/M10-EXTRACTOR-COST-20261019.md` for exact hypotheses,
component citations, the polynomial and remaining M10 work.

The previous draft was blocked by superseded local preflight rules. The
resumed compile used the revised shared `mkdir /tmp/aspis-local-lean.lock.d`
lock and capped-process check, Lean 4.32, `-j1 -M4400 -DElab.async=false`, a
private object directory and `/usr/bin/time -l`. No existing Lean module was
edited. Missing arithmetic cache dependencies were compiled first. The
no-model predecessor's retained search paths supplied a missing terminal
interface; its three direct object hashes match its original command pins.

`RawExtractorCostLedger` passes unchanged. The original
`RawExtractorCostComposed` fails because `intro H ha` binds the let-defined run
to `ha`. V2 repairs this with `intro H run ha`. The original failed receipt
contains `sorryAx` from Lean's error recovery and is **not** certified evidence.
Both missing-import failures are also retained in named directories.

`manifest.json` records successful targets, source revision and hashes,
resolved direct import source/object hashes, exit, wall time, peak RSS, swap
count and all source `#print axioms` results. Swap bytes are unavailable from
`time -l`; null does not mean zero bytes. `tools/compile.py MODULE` reproduces
individual compiles using retained caches; `tools/finalize.py` validates
receipts without rerunning unchanged proofs. No objects or archives are
committed. Historical `preflight.json` and `vm_stat.txt` describe only the
previous blocked attempt. No package-wide or formal release replay was run.

| Successful target | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | --- | --- | --- | --- |
| ActualScaledDivisorMonic | 0 | 5.349 | 2199355392 | 0 |
| ActualRawModCostBound | 0 | 7.381 | 2205974528 | 0 |
| RawExtractorCostLedger | 0 | 3.143 | 2389491712 | 0 |
| RawExtractorCostComposedV2 | 0 | 113.724 | 2338914304 | 0 |

All successful theorem audits use only `propext`, `Classical.choice`,
`Quot.sound` (some use fewer). Source revision fields identify the parent
checkout; source SHA-256 fields pin the exact tested working-tree content.
