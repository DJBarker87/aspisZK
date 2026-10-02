# R214: retain the selected copy statement through preprocessing

The isolated Aeneas candidate keeps `CopyNonOverlapping` intact in `remove_useless_joins`, classifying it with other non-inlinable effect statements. The lead inspected the exact one-line delta and validated every retained artifact checksum. No verifier source or interpreter/memory semantics changed.

The cached static release build exited 0 in 6.97 s. GNU time reports the Docker client RSS (28,336 KiB); the dedicated build slice records 564,318,208 bytes peak and zero swap. Translation of the unchanged R210 projection ran once and exited 2 in 0.15 s, child RSS 55,440 KiB, zero swaps. It now fails at `PrePasses.decompose_global_accesses`, line 2885, on the same intact copy statement. No Lean output was emitted; `#print axioms` is inapplicable. This is a diagnostic, not a verified vector lemma.

Exact source deltas, source/binary/input hashes, source revision limitations, logs, commands, caps, statuses and memory boundaries are retained in [the lead audit](evidence/r214-copy-routing/lead-audit.json). The compiled binary stays on the pinned host, identified by checksum; it is not added to Git. The Aeneas snapshot's original Git revision was not captured and is not replaced by the campaign revision.

First remaining proposition: process all copy operands without erasing the statement, then justify its memory semantics and the actual selected vector operation. Captured gamma fold and full callback/oracle chronology are still open. End-to-end privacy and soundness remain unproved. CU results 999,790 / 999,532 and all security parameters are unchanged; no benchmark or unchanged regression reran.
