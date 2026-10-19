# Unified initial-row trace facts

Focused target: `R1UnifiedInitialReads`. The final source proves the four initial-row addresses are read in the prefixed verifier trace and states the row-0 challenge equation. It introduces no extra protocol premises.

The pinned NUC runner used a 4 GiB `MemoryHigh`, 6 GiB `MemoryMax`, and `MemorySwapMax=0`. Three early attempts are preserved with exact source snapshots and compiler diagnostics; attempt d is green (exit 0, 1.55 s wall time, 3,545,852 KiB max RSS, 0 swap). `#print axioms` reports only `propext` and `Quot.sound` for both theorems.

The final Lean source hash is `2932525416efac6817cd8e0fe22c27ed0b9aac0ff7da17e5a34fcef4e41aa7fd`. The target object is retained in a deterministic archive; its member hash is `c4c39888a4969e1c3f33a0a04bb94d67f138b51e1f799e9b72eab44e00f8fd8c`.
