# G_R1 cost evidence — 2026-10-13

Read-only copies of NUC JSON/log receipts, with generated accounting and audits. No ELF, proof/public binary, key, or deployment artifact is committed.

Reports:

- [P2 reconciliation](../../docs/research/100bit-spend-path-20261013/RECONCILIATION-P2.md)
- [Authenticated tx2 coverage](../../docs/research/100bit-spend-path-20261013/AUTHENTICATED-TX2.md)
- [Complete random-mask CU](../../docs/research/100bit-spend-path-20261013/FULL-RANDOM-MASK-CU.md)
- [Rollover design options](../../docs/research/100bit-spend-path-20261013/ROLLOVER.md)

`evidence-audit.json` inventories every new capped command, including failed attempts, exact command/exit/wall/RSS/swap and repair. `*-inputs.json` records each command's existing input hashes and active-scope reservation check. `copied-evidence-sha256.json` maps all 287 copied artifacts to absolute host paths and verified SHA-256; their local file modes were set read-only after comparison. Git preserves content, not the read-only mode.

Host: `dombarker@100.108.41.90` (`nuc`). Workspace: `/home/dombarker/project-offloads/aspis-100bit-path-20261013`. New receipts/fixtures: `results/gr1-cost-20261013`; isolated native source: `gr1-cost-source`. All 32 new commands used MemoryHigh=4G, MemoryMax=6G, MemorySwapMax=0 with zero observed swap. The largest sampled aggregate RSS was below 1.1 GB. Commands expected to spend time in compilation, proof generation and the finite mutation corpus ran optimized release builds, with the existing capped recorder's ten-minute review stop.

## Contents

- `pool-{v2,v3b}-{transfer,withdrawal}-{1..5}-evidence.json`: five complete adapter runs per cell; each contains tx1/tx2, lifecycle negative cases, input hashes, simulation/execution equality and account afterstate checks. Its companion `.json`/`.log` is the scope receipt, and `-inputs.json` pins the retained ELFs and frozen native driver.
- `full-random/`: one recorded complete random tape per operation, exact proof/public hash metadata, two 5,675-case mutation corpora, positive dense/strict/authenticated trace equality and 20 individual CU measurement JSONs. Each tx2 checkpoint came from the same run's tx1.
- `mask-tape.json`: applied tape coverage counts/hashes; `mask-tape-audit.*`: separately capped audit run.
- `adapter-dense-result.json`: exact trace equality for the actual shared v2/v3b adapter proof/public inputs; `gr1/adapter_trace.rs` is the third added native example.
- `equivalence.*`: all 15 focused Rust release tests.
- `historical/`: retained source manifests, stack/build receipts, stage transfer diagnostics and the selected d18 five-run acceptance set. The P2 baseline table remains in `results/r1-precheck-20261010/REPORT-P2.md`.
- `withdrawal-stages/`: missing earlier-stage withdrawal diagnostics, with all scope receipts at the top level. The old P2 proof fails under d18 at Relation; that failure remains visible and is not used as a completed CU result.
- `rollover/`: the pre-existing v3b 255-pair transfer cap failure. Its completed suffix cost and withdrawal rollover cost are unknown; the deliverable is the allowed design note.
- `phase-accounting.json`, `phase-tables.md`, `stage-attribution.md`: generated from raw marker intervals and P2's table; sums and five-run equality checked by `gr1/reconcile.py`.
- `source-replay.json`: all 373 archive source files verified against Git blobs at `628054cd494c66dc91e4e01612c70bd164ecf276`. `native-source-manifest.json` also records the unchanged archived files and the extra workspace members used after the initial missing-member failure. `native-artifact-hashes.json` pins the resulting native binaries on the host (not copied).

## Reproduction

Check out commit `628054cd494c66dc91e4e01612c70bd164ecf276` in an isolated host workspace. Copy [native_gate.rs](../../docs/research/100bit-spend-path-20261013/gr1/native_gate.rs) and [mask_tape.rs](../../docs/research/100bit-spend-path-20261013/gr1/mask_tape.rs) into `crates/aspis-r1-cost-probe/examples/` as `gr1_native_gate.rs` and `gr1_mask_tape.rs`. Use the recorded seed and exact release commands from the receipts, with a **fresh** output path and the 4G/6G/swap-0 wrapper [run.py](../../docs/research/100bit-spend-path-20261013/gr1/run.py). No existing source file needs modification. This checkout avoids the archive-only attempt's missing-workspace-member issue.

SBF measurements execute the retained, hash-pinned ELFs; they do not rebuild them. [pool_runs.py](../../docs/research/100bit-spend-path-20261013/gr1/pool_runs.py) and [withdrawal_stages.py](../../docs/research/100bit-spend-path-20261013/gr1/withdrawal_stages.py) record the exact fixture/driver choices. Never overwrite receipts or rerun an unchanged completed gate without an identified evidence gap. `reconcile.py` and `audit.py` can recheck accounting without rerunning a verifier.

The source revision string on new resource receipts labels the runner/native source. The measured ELF is independently pinned by its input hash; d18/v2/v3b are not interchangeable artifacts. v2's retained historical build receipt does not include a full source-file manifest; this limitation is explicit in the report. For native replay, the three added examples are the only new Rust sources.

All task keys remain retained on the NUC. Local copies encountered while collecting JSON were moved into `~/.aspis-retained-task-keys/gr1-cost-20261013/` with directory mode 0700/file mode 0600; none is in this evidence tree. No key was destroyed. This was local LiteSVM work only.

These artifacts record cost and conditional parser coverage. They do not establish cryptographic soundness/privacy, a worst-case CU bound, successful rollover, or permission to deploy.
