# R205 absorb hash-call expression

R205 proves both extracted R137 absorb branches equal an explicit bind with one hash call for an arbitrary source hash. The short branch sends one packed slice; the long branch sends three slices containing state, domain/label and payload. Hash failure and divergence remain visible. The proof reuses symbolic scratch-buffer lemmas, rather than reducing 192 cells.

The focused target compiled with pinned Lean 4.32: exit 0, 1.77 seconds, peak RSS 3,719,376 KiB, zero swaps. Both complete axiom reports contain only the standard foundations. [Evidence](evidence/r205-absorb-hash-call/manifest.json) includes the exact revision/checksum, executed runner and all successful/failed logs.

Next: transport this expression to the current selected transcript, then bind the complete actual callback chronology. This proves neither a concrete hash backend law, whole callback trace, probability law, privacy nor soundness. Verifier source, CU results and parameters are unchanged.
