# Candidate CU bound — 20 October 2026

Status: IN PROGRESS. No bound or PASS is claimed.

Task base: `2318acd430b8474de01e6117248442e3ab0b17b9`, branch
`codex/cx-cu-bound5-20261020`. Candidate source binding: `c16e59e77`.
Production source will remain untouched. Frozen verifier and parked candidate
are read only. No merge, push, deployment or key cleanup is authorized.

Method: `design/PREREG-CU-UPPER-BOUND-2-20261019.md`, under the lead's
admitted split `[3,10]` ruling, and bound4's reviewed assumptions.
The campaign must reproduce candidate default/devnet/Pool pins before
measurement, then rederive executed branches, maxima and residuals,
phase/function consistency, and >=256 accepted samples per kind plus targets.
Expected heavy work: SBF/native compilation, then register-trace CFG/arm
aggregation. Every gate uses 6G high / 8G max / no swap / TasksMax 64;
reservation sum <=55 GiB; optimized Rust and four linker threads.

Host: `/home/dombarker/project-offloads/codex-cx-cu-bound5-20261020`.
Harness inherited from bound4; all new evidence must be generated for this ELF.
Large traces will be hashed then deleted. Keys and proof sidecars retained.
No Lean work is in scope; axioms audit N/A.

The packet references `C3-SKELETON-20261020.md` and
`PRIVACY-FINAL-20261020.md`; neither exists in this task base. This CU job
makes no soundness/privacy closure claim and does not depend on either file.

## Stage 1: candidate reproduction

The 59 source input SHA-256s match this branch and the prep5 source binding.
Fresh optimized capped builds reproduce all six deployed/linked candidate
verifier, devnet verifier and Pool pins; see `pins.json`. Default/devnet
`.text` is identical and replacing ID slots at 1,492,256 / 1,492,288 exactly
reconstructs the devnet file. Native release measurement/trace drivers built.
Builds so far exited zero with zero swaps; individual time/RSS receipts
are in `receipts/builds/`. No production source was edited.

## Stage 2: accepted-input sweep

All six controls reproduce prep5's CU exactly. All 746 corpus replays accept:
373 per kind, including 300 prior OS-masked random witnesses per kind. The
740 non-control proofs and publics are byte-identical to the retained original
corpus (`corpus-inventory.jsonl`). Positions span 0 through 1,048,575, with
same-page/rollover/genesis histories, fresh/prefunded markers and split 10.
Per-input measurements are in `sweep.jsonl`. These are measurements only;
branch/residual/consistency analysis is still pending.
