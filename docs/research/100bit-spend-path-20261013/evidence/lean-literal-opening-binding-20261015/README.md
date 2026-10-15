# Literal opening reader coherence and binding evidence

This bundle records two focused Lean compiles at base `b400d586a84383b19f6250c383d56db1dda0a622`. `R1LiteralOpeningCoherence` proves that the opening view, prior challenge reads, and staged row readers agree between a prefix-local view and a completed transcript when the indexed length conditions hold. `R1LiteralOpeningBinding` proves four bad-event equivalences, conditional on `LiteralMatchingData.read` succeeding on the completed transcript.

The binding theorem therefore identifies existing events with the corresponding exclusions in a successful terminal `MatchingSupport.Data`. It does not establish that accepted executions make the terminal reader succeed, and it does not supply the terminal D3 implication. The binding log contains preserved unused-simp warnings.

Both attempts exited successfully under `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, `TasksMax=128`. There are 15 standard-only axiom reports total. The deterministic object archive contains the two target objects and four direct import objects; no loose `.olean` files remain in the bundle. Exact source, object, runner, receipt, and diagnostic hashes are recorded in `source-manifest.json` and `SHA256SUMS`.
