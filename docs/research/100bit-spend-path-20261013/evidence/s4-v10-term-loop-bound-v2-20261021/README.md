# V10 typed term-loop transport

This focused packet lifts the checked V10 inner term-body transport through the Aeneas loop and applies the retained v6 successful term-loop linear-bound theorem. `v10TermLoop_eq_fixedLoopV2` proves the loops equal by congruence on their body functions; it does not unfold the loop recurrence. The success theorem consumes that equality on the same input and output.

The adapter is explicit and parameterized. This does not establish the concrete V10 source operations, full enclosing callback equivalence, or Rust/P6 `from_fn` correspondence. The prior V1 attempt timed out because `congr 1` unfolded the loop during WHNF; its source and log are preserved in the parent candidate packet diagnostics. V2 avoids that reduction.

The compile used Lean 4.32, `-j1 -M4400`, exited 0 in 2.13 seconds, peak RSS 2,238,316,544 bytes, swap 0. The runner did not capture source revision at launch; exact source and object hashes are authoritative. Axiom audits are recorded in `manifest.json`.
