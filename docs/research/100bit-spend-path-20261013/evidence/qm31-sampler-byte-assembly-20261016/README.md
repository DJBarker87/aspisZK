# Actual sampler byte-assembly loop, 2026-10-16

`ExtractedQM31SamplerBytes.lean` passed a focused Lean 4.32 check. Final source SHA-256: `340fc0e1970e9154139cc5f3b62574a44f390aa8b97a0a7f84f376f3fb7383b5`.

In namespace `AspisR1.ExtractedQM31SamplerBytes`:

- `byteWord block j` calls the same primitive `core.num.U32.from_le_bytes` as the generated sampler, on input positions `4*j` through `4*j+3`, each with a proved bound.
- `byteWords block` is the eight-word `List.ofFn` array; `wordAt_byteWords` proves every coordinate equals that specified word symbolically.
- `body_step` proves a successful actual `sampler.qm31_digits_loop0.body` iteration for every index below eight. It discharges checked multiplication, four byte reads, offset additions, the exact primitive decoder, array update and increment.
- `loop0_correct` uses the visited-coordinate invariant and decreasing measure `8-index`. `loop0_total block rank` proves the actual loop from index zero returns exactly `byteWords block`, for every initial eight-word array.
- `assemble_total block` specializes the actual repeated-zero initialization used by `qm31_digits`.

The byte input is any `Array U8 32`; no canonical-field, digit-bound, loop-success or preassembled-word premise is imposed on `assemble_total`. There is no new natural-number rank model. The theorem does not prove the four division passes, exact whole-byte rank interpretation, transcript binding, verifier call-site reachability or correctness of the Rust extraction tooling.

## Retained checks

| Attempt | Result | Wall seconds | Peak process RSS KiB | Sampled cgroup bytes | Swaps |
|---|---|---:|---:|---:|---:|
| bytes-body-a | Helper proof failure; actual bounded body checked | 2.412 | 2,651,216 | 441,524,224 | 0 |
| bytes-loop-b | Array lemma/projection proof failures | 2.413 | 2,654,252 | 446,947,328 | 0 |
| bytes-loop-c | Passed; six standard-only audits | 2.814 | 2,663,852 | 457,998,336 | 0 |

The first correction used the symbolic `List.getElem_ofFn` theorem instead of eager eight-entry simplification. The second qualified `Aeneas.Std.Array.set_val_eq` and made invariant projection types explicit for arithmetic reasoning. No generated body, bound, theorem premise, resource cap or heartbeat setting changed. All earlier source/log/receipt/audit failures are retained and separated from the final green result. The final six audits use only `propext`, `Classical.choice`, `Quot.sound`.

All jobs ran serially in separate systemd scopes with `MemoryHigh=6G`, `MemoryMax=8G`, `MemorySwapMax=0`, `-j1 -M0`. Only this changed module compiled. Its sole direct import is `AspisR1Qm31SamplerIndex.Funs`; the two generated predecessors and patched 4.32 backend were reused with exact runtime/source/import/object pins. The retained external snapshot also contains the earlier carrier bridge's unused current-QM31 cache entries; this byte module imports no arithmetic or rank model.

Host workspace: `/home/dombarker/project-offloads/aspis-r1-r18-sampler-carrier-20261016`. The archive retains all three attempts, checked source/object, source manifests, runtime/cache snapshots and the receipt-verifying setup scripts. The canonical source was compared byte-for-byte with the checked archive copy. `archive-members.json` hashes every regular archive member; `bundle-manifest.json` hashes the outer files. Native extraction and generated-source pins are retained in the separate sampler extraction evidence.
