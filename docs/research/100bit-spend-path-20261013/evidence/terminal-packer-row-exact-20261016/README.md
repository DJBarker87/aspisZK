# Exact four-QM packing and selected Poseidon row

Fifteen focused Lean 4.32 targets pass, with 37 axiom reports containing only
`propext`, `Classical.choice`, and `Quot.sound`, or no axioms. Every successful
target exits 0 and records zero process swaps. Maximum target RSS is
4,045,256 KiB. The exact source snapshots are maintained in `../../lean`.

`ExtractedMaskQmPackBase4Whole.qm31_pack_base4_success` proves that the actual
generated packer succeeds for a slice of exactly four canonical QM31 inputs,
returns a canonical value, and computes the four-coefficient tower formula.
`ExtractedMaskQmPackBase4SemanticConsumer.generated_pack_maps_to_pack4` maps
that result into the existing `R0P.pack4` model using the previously checked
concrete field map and basis compatibility. It does not assume the packer
has already succeeded. Shorter slices are outside this theorem's scope.

`RawPoseidonExternalRowExact.external_linear_lazy_row_exact` proves that the
actual candidate row wrapper succeeds for an index below four and computes
`R0P.poseidonMat4` on decoded input words. Its fixed U32 inputs need not be
canonical; the preceding raw-word proof supplies arithmetic bounds and
canonical output. This is one row, not the whole matrix layer or permutation.

## Audit and reuse

`root-review.json` independently checks all 458 original checksums, 49 compiler
attempts (15 green and 34 failed), all selected source/object pairs, raw axiom
and resource logs, three exact generated declaration blocks, and every direct
import against previously published source-bound successes or pinned libraries.
One additional source-only preflight has no compiler receipt and is not counted
as a proof attempt. Failed attempts remain diagnostic evidence only.

The packer reuses the checked reducer, tower arithmetic, concrete semantic
bridge and `R0P.pack4`. The row interpretation uses symbolic additivity and
natural-number scaling, followed by the existing matrix model. Its first
concrete-field simplification attempt hit the heartbeat limit; the replacement
proves these small symbolic facts instead of increasing the limit or unfolding
large concrete terms.

The separately green generic `Prelude` helper is not used by `Whole`: the
final proof imports `InitCopy`, which explicitly initializes with the source's
`QM31.ZERO`. The source-kit manifest predates the final slice import fix; the
original manifest/checksums are retained and `provenance/qm-pack-slice/reconciliation.json`
records the final source/object and unchanged declaration spans. The independent
review compares the final three declaration bodies with the pinned G originals.

`proofs.tar.gz` preserves the original bundle, all raw attempts, source snapshots,
objects, runner, environment, slice generator and G origins. Extract it and run:

```
python3 audit-bundle.py /path/to/bundle /path/to/aspis-repository
```

This audit uses the already-published dependency evidence named in the review;
it does not recompile unchanged modules.

## Resources and source revision

One Lean target ran at a time on the NUC: MemoryHigh=4G, MemoryMax=6G,
MemorySwapMax=0, TasksMax=128, `-j1 -M5000 -DElab.async=false`, timeout 300 seconds.
The recorded workspace base is `b40d1cfffadbdf967f84cca23ea4e7f1553d564f`;
each changed source and imported object has a separate hash. Wall time below
is the process GNU-time record; controller times are also retained in receipts.

| Target | Process wall time | Peak RSS KiB | Axiom reports |
|---|---:|---:|---:|
| ExtractedMaskQmPackBase4Array | 0:01.25 | 2,605,884 | 3 |
| ExtractedMaskQmPackBase4Arithmetic | 0:03.33 | 3,014,936 | 4 |
| Qm31PackBase4Slice | 0:01.89 | 2,607,520 | 0 |
| ExtractedMaskQmPackBase4Fragments | 0:01.90 | 3,001,392 | 3 |
| ExtractedMaskQmPackBase4InitCopy | 0:01.31 | 2,604,360 | 1 |
| ExtractedMaskQmPackBase4Prelude | 0:01.30 | 2,605,144 | 1 |
| ExtractedMaskQmPackBase4SemanticConsumer | 0:01.75 | 4,041,768 | 1 |
| ExtractedMaskQmPackBase4Semantic | 0:02.47 | 4,045,256 | 1 |
| Qm31PackBase4SliceFacts | 0:01.13 | 2,596,084 | 1 |
| ExtractedMaskQmPackBase4SourceArithmetic | 0:04.48 | 3,051,344 | 11 |
| ExtractedMaskQmPackBase4Tail | 0:01.37 | 2,991,016 | 0 |
| ExtractedMaskQmPackBase4CheckedU64 | 0:01.54 | 2,986,272 | 5 |
| ExtractedMaskQmPackBase4Whole | 0:01.93 | 3,015,328 | 1 |
| RawPoseidonExternalRowExact | 0:01.78 | 3,809,536 | 1 |
| RawPoseidonRowField | 0:02.15 | 3,334,048 | 4 |

No enclosing terminal theorem, whole verifier theorem, security theorem,
privacy claim or production runtime adoption is established by this batch.
