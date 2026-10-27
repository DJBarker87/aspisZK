# D325 merged candidate integration gates

Source `03905a52594fadc50a1c00ab3f240a79632e8ffd`; branch `codex/pv-integ4-20261027`. No implementation source edits. Target not yet established.

Stages pending. Timing gate is expressly not authorized for this job. All native builds use serial capped scopes (6G/8G, swap0, TasksMax64), optimized -j4; preflight and in-scope admission require allowed:true and exit0. IDs39500–39599 reserved but no Lean compilation planned. Kani0.

## Stage 1: verifier ELFs — PASS

Fresh candidate rebuilds match all three requested SHA256 pins; see `elf-summary.json` and per-build receipts. Default 1,563,728 bytes,54.250s,684,548KiB RSS; devnet 1,563,728 bytes,35.294s,685,392KiB; Pool605,704 bytes,47.509s,677,856KiB. All exit0/swap0. The initial default launch failed before compilation on a non-executable job-local diagnostic wrapper; mode corrected, distinct retry receipt retained. No pin mismatch. `source-identity.json` verifies every exported input (7,290 files) against exact git source bytes.
