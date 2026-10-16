# Source-byte rank on the current backend, 2026-10-16

The unchanged source-byte rank chain passed focused Lean 4.32 checks against the pinned current Aeneas backend. No mathematical source, generated sampler body, arithmetic model, axiom whitelist or resource limit changed. The source closure is pinned to `834ae63ed267c7b8aa7031d2d7f7edaac591114c`.

The final audit checks exactly:

- `AspisV8R19.SamplerWordRead.four`
- `AspisV8R19.SamplerWordBridge.source_word`
- `AspisR1.SourceSamplerByteRank.word_value`
- `AspisR1.SourceSamplerByteRank.run4_bytes`
- `AspisR1.SourceSamplerByteRank.rank_lt`

All five report only `propext`, `Classical.choice`, `Quot.sound` (or a subset). They connect the existing four-byte primitive, reversed eight-word numeral and four-pass arithmetic model to the existing rank of all 32 bytes. The actual new sampler's dependent composition is a separate worker-C target, not a conclusion of this bundle.

## Cache and audit boundaries

The initial 65-module inventory found 55 cache candidates. Nine older Aeneas-dependent objects were rejected because their backend objects differed from the current backend, despite sharing Lean 4.32. The final closure reuses 13 recently checked arithmetic-model modules and 40 historical pure modules; 12 existing modules were compiled from unchanged sources.

`SamplerWordRead` compiled successfully, but its full audit **failed**: old `unwrap_success` and `read_success` depend on `core.fmt.Formatter`. That failure remains intact. Its object is explicitly marked as a mixed-axiom artifact, never as a standard-only module. Only its `four` definition enters the accepted rank proofs; the separate narrow and final audits verify this scope. No claim about the old read/unwrap implementations is accepted. Generated Types/Funs compiled with zero requested audits; this does not assert a whole-module axiom result.

A read-only `Lean.readModuleData` probe also found a false historical source/object correspondence: cached `AspisFormal.CircleGroupOrder` imported `Mathlib`, while its pinned source had 15 focused imports. The other 58 inspected import headers matched their source headers after duplicate `Init` entries were removed. The mismatched object was rejected. Exactly `CircleGroupOrder → R0C.ModuloField → R1SamplerBlockRank → R1SourceSamplerByteRank` was rebuilt; no Mathlib-root expansion occurred. The Circle proof already reduces its concrete checks to 30/31 squarings via `sq_iterate`; no large exponent iteration or proof rewrite was introduced.

## Retained verification

The final repaired checks took 3.417, 2.012, 2.010 and 2.010 seconds respectively; the five-declaration audit took 1.809 seconds. All used one serial job with `MemoryHigh=6G`, `MemoryMax=8G`, `MemorySwapMax=0`, `-j1 -M0`. Across all 17 retained target attempts, peak process RSS was 6,654,856 KiB, maximum sampled cgroup memory was 843,661,312 bytes, and process/cgroup swap remained zero. `check-summary.json` retains every target's source hash, timings, memory, exit and axiom reports.

Two import failures are retained separately from successful checks. The first required a per-run unified namespace directory: symlinks refer only to pinned snapshot objects or receipt-checked new objects, and every source/destination/hash is journaled. Conflicting hashes fail closed. The second exposed the Circle cache mismatch above. Already-green unaffected targets were reused; no full manifest replay or dependency build ran.

The final host workspace is `/home/dombarker/project-offloads/aspis-r1-r18-sampler-rank-final-20261016`. Its external snapshot SHA-256 is `ddea49cae41e5cbe17961db56cc7d882075df4fc966cb90af20e006b0d94ed1b`. The archive retains all three staging workspaces, failures, final sources/objects, receipts, runtime/import pins, mixed-module exclusions, rejected-cache evidence and overlay journals. It omits duplicate symlink trees. `archive-members.json` hashes all 223 regular members; `bundle-manifest.json` hashes the outer files.
