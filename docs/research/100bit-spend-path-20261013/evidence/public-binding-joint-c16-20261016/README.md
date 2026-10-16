Eight focused targets passed over A's current c16 caller universe. The old
preparation Types/Funs and their entire reverse-import closure are excluded
from the external cache; every affected C dependent was compiled on the new
objects. This is the coherent current-universe result, with no old/new object
mixing. `verify.py` passes read/hash-only: 131 members, 19 standard-only axiom
reports, all 79 original generated declarations unchanged by token hash.

| Exact target | Exit | Wall seconds | Peak RSS KiB | Swap | Reports |
| --- | ---: | ---: | ---: | ---: | ---: |
| AspisR1PublicPreparation.Types | 0 | 2.154 | 2,661,936 | 0 | 0 |
| AspisR1PublicPreparation.Funs | 0 | 4.362 | 2,728,248 | 0 | 0 |
| ExtractedPublicPreparationSuccess | 0 | 1.722 | 2,637,116 | 0 | 3 |
| ExtractedPreparationSerializerFields | 0 | 1.938 | 2,642,740 | 0 | 3 |
| ExtractedPreparationSerializerLoop | 0 | 1.943 | 2,645,872 | 0 | 4 |
| ExtractedPreparationSerializerWhole | 0 | 8.607 | 3,899,308 | 0 | 2 |
| ExtractedPublicPreparationBinding | 0 | 2.156 | 3,851,088 | 0 | 4 |
| ExtractedFirstCallerReachability | 0 | 2.159 | 3,867,244 | 0 | 3 |

Every scope used 6 GiB MemoryHigh, 8 GiB MemoryMax and MemorySwapMax=0;
all final receipts record zero process/scope swap and no dependency/package
build. Sources are committed at `162f2a4d0`; current raw caller extraction is
`c16ab4d76`. Exact source, runtime, producing import/object keys, commands,
status, wall time, RSS, swap and `#print axioms` are retained. Generated module
checks request no theorem audit; the six dependent proof targets provide the
19 reports, containing only propext, Classical.choice and Quot.sound.

The current carrier uses the original five naming expansions with a checked
inverse; all actual function bodies are unchanged. Current Types source hash
is `34d88375…f4220`, Funs `e98bb123…55650`. The original and current raw modules
and the complete per-declaration inventory are in the archive.

The initial Types check passed before the runner rejected an old/current
module overlay conflict. The corrected snapshot excludes every reverse
importer and reuses that green Types result. An external Lean process then
interrupted Whole twice and Binding once; the guard stopped only this
worker's process. Every interrupted receipt is retained. A focused in-process
resume reused its cryptographically verified external snapshot, rechecked each
external stat identity and every source/producing object key, and reused all
green predecessors. Only interrupted targets were retried.

The final caller-prefix theorem derives actual decoder success and equality
of the public supplied to its explicit downstream continuation with the fixed
decoded projection. The actual helper supplies serializer `hs` for both
variants. Downstream tx1-to-helper reachability, SDK/runtime preservation and
custody remain separate. No SBF rebuild or runtime harness was run.
