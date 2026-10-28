# LOG D362 recovery inventory

Recovered at HEAD03984c6b6e on the exact assigned worktree/branch. No Kani/Lean/native invocation was rerun during recovery. Host had no live own process. K16 was the only launched output missing locally; collected read-only after completion. It timed out, exit124, wall900.71s. Its GNU-time RSS excludes the killed solver descendant, as for the earlier timeout receipts.

The initial51 git status entries expand to126 files; `recovery-initial-files.json` records every file, size and SHA256 before recovery. All are within the assigned evidence/tools paths. They consist of completed receipts/admissions/logs, targets, table/README updates, and own wrapper corrections. No partial source or invalid proof was promoted. Historical failed/cancelled/time-out evidence is retained and labelled. Host textual source freezes are now collected alongside receipts; differing local/host diagnostic snapshots are retained separately.

| Run | Harness | Role | Result | Wall | Receipt |
|---|---|---|---|---|---|
| K01 | path_join8 | positive | CANCELLED | None | [K01](K01/receipt.json) |
| K02 | path_join8 | positive | TIMEOUT | 15:00.40 | [K02](K02/receipt.json) |
| K03 | path_join8 | control | TIMEOUT | 15:00.00 | [K03](K03/receipt.json) |
| K04 | string_ascii8 | positive | PASS | 4:50.58 | [K04](K04/receipt.json) |
| K05 | string_ascii8 | control | FAIL | 1:22.28 | [K05](K05/receipt.json) |
| K06 | string_scalar | positive | PASS | 2:03.41 | [K06](K06/receipt.json) |
| K07 | string_scalar | control | FAIL | 0:07.41 | [K07](K07/receipt.json) |
| K08 | push_ascii1 | positive | PASS | 1:44.32 | [K08](K08/receipt.json) |
| K09 | push_ascii1 | control | FAIL | 0:03.87 | [K09](K09/receipt.json) |
| K10 | join_one_byte | positive | TIMEOUT | 15:00.67 | [K10](K10/receipt.json) |
| K11 | join_one_byte | control | FAIL | 0:11.76 | [K11](K11/receipt.json) |
| K12 | string_path | positive | PASS | 0:11.47 | [K12](K12/receipt.json) |
| K13 | string_path | control | FAIL | 0:11.02 | [K13](K13/receipt.json) |
| K14 | string_push | positive | PASS | 4:12.00 | [K14](K14/receipt.json) |
| K15 | string_push | control | FAIL | 0:21.00 | [K15](K15/receipt.json) |
| K16 | join_two | positive | TIMEOUT | 15:00.71 | [K16](K16/receipt.json) |

Positive/control pairs at recovery: path_join8 K02 TIMEOUT / K03 TIMEOUT; string_ascii8 K04 PASS / K05 intended FAIL; string_scalar K06 PASS / K07 intended FAIL; push_ascii1 K08 PASS / K09 intended FAIL; join_one_byte K10 TIMEOUT / K11 intended FAIL; string_path K12 PASS / K13 intended FAIL; string_push K14 PASS / K15 intended FAIL. join_two K16 TIMEOUT, control K17 not launched. K01 cancelled selector diagnostic receives no credit.

Budget charged16/30 Kani,2/10 Lean. Remaining14 Kani and8 Lean attempts. Admission refusals never count as launched compiles. Ruling(m') now applies to same unlaunched IDs and the full180s cooldown.

NBZ_K042 is recorded for pattern review only, with no credit changes. See `observer-pattern-audit.json`.
