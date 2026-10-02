# R332 saved-evidence audit

Read-only verification of the promoted R332 bundle. No Lean command was run and no tracked file was changed.

Result: PASS. All bundle checksum entries match; the target is byte-identical to its saved source copy and has the manifest SHA; the checkout revision matches the recorded revision. The successful log records exit 0, 1.62 s wall time, 3,712,452 KiB GNU-time child peak RSS, and zero swaps. The runner specifies `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`, and Lean `-j1 -M4500`.

All five complete `#print axioms` reports match the saved axiom text and contain only `propext`, `Classical.choice`, and `Quot.sound`. The theorem uses R329’s explicit nonempty and encoded source-read conditions; there is no separate capacity, nonzero, or successful-execution premise. Capacity is derived in R329, and zero values are allowed. The bundle includes actual R317 `Slice.last` on `Vec.deref`. Full guard, second vector, inverse, independent Std/compiler correspondence, and callback/security remain open. The failed result-constructor plumbing log and unverified worker draft are retained.

Machine-readable checks: `audit.json`.
