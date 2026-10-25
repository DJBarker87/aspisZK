# S1 Claims: capped extraction and complete accepted parent, 2026-10-25

Status: **local source TOTAL and explicit-primitive ACCEPTED-ONLY results; S1/S6 and the 100-bit target are not established**. S2 remains transferred. No frozen production source was changed or candidate adopted.

The authoritative frozen source remains `25866ec331cc7ce27dd9956609c11d32fa8fa58a`, with powers overlay `29cbab431742f7e899870595167efa193a379f0a`. Safe Claims candidate `891a213f79` and the finite unrolled proof reference are unadopted. Existing frozen/safe control evidence (`d05f5aa31d`, `98e271b3ad`) retains its allocator, normal-return decoder and initializedness qualifications. It is not whole execution equivalence.

## What actually ran on the NUC

Following the owner's instruction to use additional memory, the source-only extraction ran in our own user scope with `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, `TasksMax=64`, a 600-second runtime guard and verified `memory.oom.group=1`. Fresh conservative host admission preceded the scope and both phases. No privileged action, unrelated process termination or another session's build directory/cache was used.

The initial 8 GiB request was refused before starting a compiler by the recorded admission calculation; 6 GiB fitted. This was not an extraction out-of-memory failure. Historical r1–r9 receipts remain committed. The original safe-loop translation hit Aeneas's shared-borrow loop collapse; finite unrolling avoids that translation limitation. Later failed selector/alignment experiments were corrected, not retried unchanged with larger caps. Full error and field carriers were preserved.

Successful final extraction: `evidence/s126-current-caller-20261021/s1-claims-nuc-extract-run10/`:

| Target | Exit | Wall seconds | time-v peak RSS KiB | Swap |
|---|---:|---:|---:|---:|
| Charon, exact source/selectors in charon-input.json | 0 | 0.352867785 | 200288 | 0 |
| Aeneas, exact command in aeneas-input.json | 0 | 0.421434683 | 79904 | 0 |

The retained warmed-workspace cgroup samples report `memory.peak=95047680`, zero high/max/OOM events; these are distinct from time-v process accounting and are not substituted for it. Both source/tool postchecks passed; LLBC `has_errors=false`. LLBC and binaries are excluded. Compiler, driver, nightly cargo/rustc, Aeneas, dynamically loaded libraries, source files, commands and controller are pinned in the packet. Tool invocations and failures are source extraction evidence, with `#print axioms` inapplicable until Lean checking.

The native safe-loop/unrolled comparison was already checked at `s1-claims-unrolled-v2`: exit 0, 23.643927916 seconds, peak RSS 1462878208 bytes, sampled aggregate 1786724352 bytes, swap 0, 0/1029 failures and 4/4 covers. It uses explicitly cut normal-return decoding and allocator operations; it does not establish actual allocator effects or original unsafe storage initialization.

## Maintained checked source and claims

`S1ClaimsUnrolledTypesV1.lean` preserves full Prefix, ValidatedRecord, QM31, both Error enums and reserve-error carriers. Derived enum instance namespaces are explicitly repinned to avoid generated name collisions. The unused external Alignment import is removed; the real standard Layout type is retained. No dummy Alignment type is installed.

`S1ClaimsUnrolledHelpersV1.lean` preserves complete emitted map_err, clone/copy/zero, getter/constructor and error-closure definitions. `helpers-binding.json` identifies every exact emitted chunk. Generated axiom templates and generated resource-option overrides are provenance only and are never imported into maintained proofs.

`AspisS1ClaimsSourceReads.record_total` proves, for every complete Prefix and every U8 row, existence of a normally returned source result. Invalid rows return the actual InvalidRow error. Valid rows derive the cast and array-index bounds. `validated_record_total` then proves the actual constructor is TOTAL. `record25_exact` derives the exact row25 frame, lookup and token from Prefix without an independent parser-success, index-success or range hypothesis. These close local R22 getter/constructor obligations, not Claims allocation or whole SDK totality.

`S1ClaimsUnrolledParentV1.lean` preserves the complete emitted heap.filled and Claims bodies, mechanically exposing only four remaining external operations as ordinary functions: reserve, into-boxed-slice, slice-to-fixed-array, and decode_k. All argument types, errors, failure/divergence carriers and branch order remain explicit. `parent-binding.json` and the checker validate the complete source chunks and precisely these substitutions. This is not a concrete instance of those four functions.

`AspisS1ClaimsUnrolledAccepted.accepted_rows` has the enclosing premise

```
candidate_claims.claims ports prefix = ok (.Ok out)
```

and derives one frame and three rows such that the actual Prefix row25 lookup succeeds, the SAME token is decoded at offsets 0, 29 and 58 with N=29, each decode succeeds with its corresponding row, and the complete returned three-row array equals those rows. It derives the bounded array read/set operations and proves that all initial array contents are overwritten. There are no independent child-success or output-correspondence premises.

This removes child-success hypotheses from analysis of this complete parameterized parent. It does **not** remove a concrete-primitive or extraction hypothesis from the existing original SDK theorem. Quantification is over ordinary primitive functions; no proposition or opaque replacement carrying the desired conclusion is installed. It must not be reported as original frozen native Claims, S1, S6 or the release theorem.

| Focused Lean target | Attempt | Exit | Wall s | Peak RSS bytes | Swap |
|---|---|---:|---:|---:|---:|
| S1ClaimsUnrolledTypesV1 | types-v2 | 0 | 2.926412792 | 2263941120 | 0 |
| S1ClaimsUnrolledHelpersV1 | helpers-v1 | 0 | 3.431235084 | 2242445312 | 0 |
| S1ClaimsSourceReadsV1 | source-reads-v2 | 0 | 6.476146250 | 2254290944 | 0 |
| S1ClaimsUnrolledParentV1 | parent-v1 | 0 | 13.729688167 | 2257010688 | 0 |
| S1ClaimsUnrolledAcceptedV1 | accepted-v1 | 0 | 2.963408666 | 2260860928 | 0 |

All commands used the one-job atomic local lock, `-j1 -M4400`, exact direct-import and tool hashes, and warm caches. Each smallest changed target was checked; no unchanged full replay was launched. Every maintained declaration audit is empty or a subset of `propext`, `Classical.choice`, `Quot.sound`. Failed types-v1 / source-reads-v1 elaborations are retained and excluded; recovery `sorryAx` in a failed audit is not accepted evidence. Successful source snapshots equal current maintained modules. This is not a final coherent release dependency replay.

## Exact remaining boundaries and next integration

1. Bind the four primitive functions to actual pinned decoding and Std/native allocation/conversion semantics, including errors, state effects and cleanup. Existing full decoder/parser results must be imported with complete nominal field/error mappings and source pins; no parser re-proof is required.
2. Establish original unsafe Claims initializedness and compose the source/control/decoder/allocation checks. The retained Kani union-pointer limitation was not a memory-cap failure. Alternatively, adopting safe Claims requires a source decision plus allocation/effect, caller, cost and artifact re-pin gates. Neither path has been silently chosen.
3. Compose this Claims result through actual Prepared::new, prepared_claim, tx1_prepare/tx1 and the same SDK execution, retaining complete challenges, reused powers and scratch state. Existing native word/control and accepted 87-cell canonicality evidence remains reusable with its published boundaries.
4. S6 decoded-public reuse is checked at its conditional SDK/source boundary. The original/current SDK, shared context/kernel and release-artifact composition remain open with the relevant integration owner. This packet makes no new S6 closure claim and does not touch S2.

Read-only source-only packet check: `python3 tools/s1-claims-unrolled-20261025/check.py`. It validates 120 source/evidence hashes, successful receipts, exact complete parent/helper factoring, accepted axioms and absence of imported templates or compiled artifacts. It does not rerun compilers or claim missing native bindings.
