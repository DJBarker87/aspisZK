# Executable natural row indices for the actual push traversal

The ascending row traversal now uses an explicit total Nat-to-Usize constructor. Its value theorem shows that reduction modulo the Usize word size is inactive for every in-range source index. Together with the retained global raw phase bound and canonical row operands, this produces the SafeRows execution without an independent arbitrary indexAt function.

Actual source-array operand correspondence, phase-bound initialization/preservation, the completed query counter increment, and the full Rust caller refinement remain open. This is a source-shaped traversal using actual generated push operations, not a completed caller proof.

Lean 4.32 exited 0 in 13.42 seconds, peak RSS 2,208,808,960 bytes, zero process swaps; printed axioms are standard only. Exact source/object/import hashes, command, source revision and logs are retained. This is focused working evidence, not a unified release replay.
