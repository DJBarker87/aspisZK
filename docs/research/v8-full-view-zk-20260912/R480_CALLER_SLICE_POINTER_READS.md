# R479–R480: selected caller slices and pointer reads

Both focused targets compiled in the pinned Lean 4.32 cached workspace at
source revision `2d1b4db406d2fb1fe57204665b7603ff56949ee8`.

R479 uses the existing pinned Aeneas `Vec.index` / `SliceIndexRangeUsizeSlice`
primitive, rather than introducing a range-index contract. Its universal result
theorem preserves the exact successful element list and the primitive's panic
on invalid ranges. For each selected range, `359..388` and `388..417`, it derives
the required vector bound, exact length 29, and every indexed value from the
successful range result. No load-success premise or canonical-field assumption
is added. This is execution of the provided Aeneas range primitive associated
with these actual source expressions, not a whole native caller execution proof.

R480 connects those successful range results to the existing 64-bit pointer
offset and allocation-read interpretation. Every index below 29 reaches the
same selected slice element. The conditions include the explicit heap lookup
and **`a.cells = v.val` memory-image premise**. It derives the slice bound and
the read result; it does not derive that memory-image premise for native Rust.
No whole fold, reference validity, aliasing, lifetime, or frame contract is
assumed to have been proved.

The source association is the frozen callback at SHA256
`4f8f80e0847ec004a56fc693f6096308090de5f3cbed35722dba330afaa9820f`,
with the complete selected R440 graph at SHA256
`96135e91c71f93dcd3aeec7b693eb737e7cf05027456ca973242cf2586088c48`.
The graph's Fun0 source text, full callback copy, exact ranges and primitive
association are retained in the evidence. This association is not a
kernel-certified JSON decoder or a new proof of Rust's range implementation.

| Target | Exit | Wall time | Peak Lean RSS (KiB) | Swaps | Complete axiom reports |
|---|---:|---:|---:|---:|---:|
| R479CallerBatchSlices.lean | 0 | 1.91 s | 3,718,116 | 0 | 9 |
| R480CallerPointerReads.lean | 0 | 1.60 s | 3,716,424 | 0 | 2 |

All eleven reports use only `propext`, `Classical.choice`, and `Quot.sound`.
None contains `sorryAx`. Exact source snapshots, checksums, direct imports,
revision, exit status, commands, full logs and axiom output are saved in
[evidence/r479-r480-caller-slice-reads](evidence/r479-r480-caller-slice-reads/).
Failed elaborations and the successful intermediate R479 before adding the
public success-image theorem are preserved separately. The final successful
targets were not replayed after promotion.

The jobs used `lake env lean -j1 -M4500`, `MemoryHigh=5G`, `MemoryMax=7G`,
`MemorySwapMax=0`, `TasksMax=128`. Peak RSS is GNU time's Lean-child reading.

## First remaining proposition

Derive the actual native reference/allocation image and lifetime/frame
conditions, then bind the selected Fun70 raw dereference and mutable callback
return to the existing fold execution. The Aeneas slice value alone carries
neither address nor provenance; the present results cannot discharge this
missing bridge by themselves. The pinned raw-pointer backend still rejects
native dereference. Do not replace it with an unproved library or memory
contract. Preserve the optional UB checks and all cleanup/unwind paths.

Full freeze extension and callback chronology, universal joint C1/H1/G
compatibility, whole-view simulation and shared-oracle probability accounting,
coherent pre-beta quotient extraction and optimized-to-source soundness remain
open. No end-to-end privacy or security claim is made. Verifier source and
security parameters remain unchanged, preserving 999,790 / 999,532 CU without
rerunning benchmarks or unchanged regressions. No deployment, merge, transaction
or wallet operation occurred.
