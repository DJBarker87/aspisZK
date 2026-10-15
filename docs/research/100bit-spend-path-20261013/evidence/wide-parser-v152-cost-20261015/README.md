# Wide parser v1.52 local SVM reuse gate

This bundle records the single `pool_gate` test run for the v1.52 wide-parser ELF. The gate reused the same proof and public bytes as the earlier v1.52 candidate run. The driver, pool, registry, ELF, proof, public input, and recorder hashes are pinned in `results/cost-input-pins-b.sha256`; fixture copies are retained in `task-artifacts/`.

The gate did not pass. Stage 1 failed with `InstructionError(3, ComputationalBudgetExceeded)`; the program log reports consumption of 1,399,494 out of 1,399,550 units. The driver produced no result JSON, terminal-stage measurement, serialized-byte count, or settlement flags. Those fields are unavailable because execution stopped at stage 1. The earlier v1.52 candidate succeeded at stage 1 with 1,390,128 CU / 295 bytes and terminal with 1,293,571 CU / 879 bytes, so this failure's reported stage-1 consumption is 9,366 CU higher; this comparison does not imply a terminal result.

Attempt `a` was rejected by the gate before simulation because its output directory had been pre-created. Attempt `b` used a fresh nonexistent output directory and reached the actual gate. Both attempts and their resource receipts/logs are retained. No further gate was run. The successful stage-1 execution, terminal stage, and settlement were not observed for this candidate.

The second task directory contains generated task keys and fixture copies. Key files remain on the NUC at mode 0600 and were not copied or deleted; names, modes, sizes, and fixture hashes are listed in `results/task-retention-inventory-b.txt`. This bundle reports a local test only and makes no broader runtime claim.

A read-only phase comparison against the prior exact-proof log is in `results/phase-cost-comparison.md` and `.json`. The first recorded divergence is at `r1:parsed` (+7,253 CU cumulative); by `r1:query:10` it is +24,774 CU. Merkle checkpoints match and each query interval adds 139 logged CU. The new run then fails before the prior `checkpoint-write` marker.
