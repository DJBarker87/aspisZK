# R326 saved-evidence audit

Read-only consistency audit of the promoted R326 evidence. No Lean command was run and no tracked file was changed.

Result: PASS. The evidence bundle checksum entries all match; the promoted Lean file is byte-identical to its saved source copy and matches the manifest SHA. The recorded source revision matches the checkout. The successful log records exit 0, 1.54 s wall time, 3,713,760 KiB GNU-time child peak RSS, and zero swaps. The runner explicitly specifies `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`, and Lean `-j1 -M4500`.

All three requested `#print axioms` outputs match the saved axiom report after whitespace normalization (the last output is line-wrapped in the log). Each contains only `propext`, `Classical.choice`, and `Quot.sound`.

The theorem signatures are model-only selectors. `actual_output_selector` requires the exact append equation `hout : out.val = px.val ++ prefixValues f i n p` and an explicit in-range bound. There is no nonzero hypothesis; the note explicitly allows zero products. No source execution, caller invariant, or full-batch correspondence is claimed. The rejected initial shift-plumbing log and unverified worker draft are retained in development history.

Machine-readable checks: `audit.json`.
