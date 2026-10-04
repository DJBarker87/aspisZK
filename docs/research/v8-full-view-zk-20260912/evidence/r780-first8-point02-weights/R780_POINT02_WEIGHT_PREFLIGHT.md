# R780 point-0/point-2 weight preflight (partial)

The exact R772 source basis transports and finite gather equations compile for the first eight selected `pointWeight` indices: 0–3 and 92–95, for both fixed points 0 and 2. The chunk 92–95 includes both the single and nested gather schedule. The package preserves all earlier R780 attempts, including failed drafts.

The five selected green sources are `R780Point02WeightSharedChunk00.lean`, `R780Point02WeightChunk00P0.lean`, `R780Point02WeightChunk00P2.lean`, `R780Point02WeightChunk01P0.lean`, and `R780Point02WeightChunk01P2.lean`. Each run used the pinned cached Lean workspace with `-j1 -M4500`, cgroup `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`; exact timings, RSS, source hashes, complete axioms, import pins and logs are in `manifest.json` and copied receipts/logs. All reported axioms are standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).

The `generate.py` check passes after correcting support-module indexing: leaf chunks are grouped by sorted leaf-list position, not by numeric leaf value divided by 32. One consumer compile failure exposed this mismatch; its receipt and source are retained.

This is a partial symbolic model proof of weight expressions only. The set comprises 8 of 343 scheduled positions. It does not close actual callback chronology, full prefix compatibility, sampler/challenge laws, privacy, or soundness.
