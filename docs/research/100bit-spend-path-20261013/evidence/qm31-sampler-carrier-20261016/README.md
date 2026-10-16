# Actual QM31 sampler wrapper and fixed carrier bridge

`ExtractedQM31SamplerCarrier.lean` passed a focused Lean 4.32 check. The source SHA-256 is `e2402fec087e8f4d6a21b5786acd3e2969b55a9f7ade0be74c1727ed379bddbc`. No generated sampler or current arithmetic source was changed.

`AspisR1.ExtractedQM31SamplerCarrier.qm31_sample_of_digits` takes precisely actual generated `AspisR1Qm31SamplerIndex.sampler.qm31_digits block = .ok ds`. It proves actual `qm31_sample block = .ok (packed ds)` by discharging the four bounded array indices and both generated `CM31.new` calls. The four packed coordinates are `ds[0], ds[1], ds[2], ds[3]` in source order.

`toCurrent` and `fromCurrent` explicitly copy all four coordinates between the sampler carrier and the unchanged current arithmetic carrier; both roundtrips and injectivity are proved. `packed_current_canonical` consumes four explicit `<2147483647` bounds. `decode_toCurrent_eq_iff` reuses the existing `ExtractedCurrentQM31Equality.decode_eq_iff` with both canonicality premises explicit. No arithmetic was re-extracted or re-proved.

The digit-loop totality, exact byte-rank/digit formula, canonical digit bounds, transcript connection and verifier call-site reachability remain separate obligations. In particular, the actual-digits-success premise is not replaced by a handwritten model conclusion.

## Focused checking

| Attempt | Result | Wall seconds | Peak process RSS KiB | Sampled cgroup bytes | Swaps |
|---|---|---:|---:|---:|---:|
| carrier-a | Local proof failure | 1.811 | 3,019,752 | 467,587,072 | 0 |
| carrier-b | Passed, nine audits | 2.012 | 3,025,976 | 480,501,760 | 0 |

Attempt A failed only because machine-size literal values in four `Fin 4` indices were not definitionally the corresponding Fin numerals. Attempt B added four explicit finite equalities for 0–3; it changed no premises or generated bodies. Failed source/log/receipt and its failed axiom audit are retained separately. Final audits report either no axioms or only `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx` remains in the final target.

Each attempt compiled only this file in its own host systemd scope, with `MemoryHigh=6G`, `MemoryMax=8G`, `MemorySwapMax=0`, one Lean thread and `-M0`. The 19 prerequisites were reused: two newly generated sampler modules and the 17 unchanged current-QM31 dependencies already checked in R17. The read/hash snapshot extension checks each predecessor's source, imports, runtime, successful receipt and actual object hashes. It selects no 4.31 objects and performs no predecessor or backend build. Frozen source-manifest copies prevent unrelated later staging from invalidating the observed provenance.

Host workspace: `/home/dombarker/project-offloads/aspis-r1-r18-sampler-carrier-20261016`. `carrier-evidence.tar.gz` retains both attempts, final source/object, scripts, original and final external snapshots, import receipts and runtime/cache pins. `archive-members.json` hashes every regular member. The outer files are hashed by `bundle-manifest.json`. The canonical source was compared byte-for-byte with the checked archive copy before committing.
