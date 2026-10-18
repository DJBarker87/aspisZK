# Actual extracted decoder: output-to-byte readback

Four accepted focused proofs extend the preceding whole-wrapper canonicality result. They cover the extracted indexed candidate, not an adopted production migration or full source/runtime soundness theorem.

- `AspisR1DecodeKFullLoopReadback` carries the actual row index through the generated loop and proves every stored row comes from its corresponding actual helper result. The earlier attempted readback incorrectly used the state's row where the statement quantified another index; the accepted proof threads row i explicitly rather than adding a free equality premise.
- `AspisR1DecodeKFullSuccessReadback` recovers the checked byte offset and per-index actual helper successes from whole `decode_k` success, including the exact field values stored in the result.
- `AspisR1DecodeKFullValueTrace` traces helper success through checked multiplication/addition, the payload, sixteen sequential indexed reads, `Array.make`/`to_slice`, and the actual field parser call with its actual successful output.
- `AspisR1DecodeKFullSuccessIndexedParser` composes these results: whole-wrapper success exposes the indexed source operations and successful parser input for every returned value. There is no intermediate assumed parser-success premise.

## Scope and source pins

The original production wire source SHA256 is `3a6f30708d5cd8de323438a5b5de479cc59d1c8234958197c3a033a0204256f3`. The indexed candidate SHA256 is `47562d76a47ba602aacbbdd61c9b97c4429ba9700aa96e8ea49d3c4ccab9b444`. Its original generated Funs source SHA is `a0bf0fcb29f13a10328b0bbdda0954bc96e531e8b0f780a0aebf6cd4ee5cb6a5`; the import-adapted Funs source SHA is `9cfa90cf12f476cd1d55c247b216ce5c8734566056fc7a6e9385ad887b26247f`. Existing canonicality/extraction packets preserve that chain. `b302c0d49` in the original receipts is a historical campaign context, not a claim of equality with the current worktree or production source. Exact proof and dependency source/object hashes control these results.

Still open: production/candidate equivalence and adoption, totality and no-panic/input-range obligations, the remaining verifier/caller/account/commitment and sampler bridges, and full soundness/privacy composition. No production source or deployed artifact changed here.

## Evidence

The original per-target receipts, command records, preflight inventories, watcher samples, time logs and standard-only axiom reports are retained. All four checks exited zero on pinned Lean 4.32, under NUC cgroups High3GiB/Max3584MiB/SwapMax0 and Lean -M3200; swap samples were zero. The sampled cgroup charge is not process RSS: `accepted-targets.json` records the actual `/usr/bin/time` maximum RSS separately. The original aggregate manifest is copied unchanged and uses historical absolute paths; local packet paths preserve the corresponding source/evidence bytes. OLean binaries and caches are not committed. No unchanged full regression was repeated.
