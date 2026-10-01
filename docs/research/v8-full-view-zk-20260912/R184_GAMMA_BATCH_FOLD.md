# R184 closed gamma batch fold

R184 composes the actual R174 gamma closure body, closed by evaluating its borrow writeback, with R183’s generic default fold. For arbitrary canonical encoded field values, it proves the exact weighted sum and final power `power * gamma ^ length`; gamma remains fixed. The slice corollary starts each batch at source `ZERO` and power `ONE`, with the remaining suffix explicitly equal to the encoded inputs. No callback failure is assumed away: the field execution lemmas establish success for these canonical values.

The explicit `closedGamma` dictionary is an adapter. It is not claimed to equal the currently mismatched captured-borrow dictionary printed by the full extraction, nor to establish the selected pointer-based slice override. The raw backward function is applied at every iteration.

The focused target compiled on the pinned capped Lean 4.32 cache: exit 0, 1.94 seconds, peak RSS 3,720,332 KiB, zero swaps. All three complete axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`. Failed draft sources and complete logs are retained in the [evidence](evidence/r184-gamma-batch-fold/manifest.json).

Next: establish the actual captured-borrow and selected slice correspondence, vector extension, and complete callback chronology through rho including every failure and oracle call. End-to-end privacy and soundness remain open. Verifier source, CU evidence and all security parameters are unchanged; no CU or unchanged regression rerun was performed.
