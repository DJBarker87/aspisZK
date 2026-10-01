# R187 generic default fold over the vector iterator

The extracted generic `Iterator::fold` default body over the existing Aeneas vector into-iterator model equals a list fold on all remaining owned values. It visits them in order, carries the closure state, and preserves arbitrary callback errors and divergence. It requires no extra callback correctness premise.

The focused target compiled in the pinned capped Lean 4.32 cache: exit 0, 1.20 seconds, peak RSS 2,534,468 KiB, zero swaps. Its complete axiom report contains only `propext`, `Classical.choice`, and `Quot.sound`. The source and initial failed draft are retained with both complete logs in the [evidence manifest](evidence/r187-default-vec-fold/manifest.json).

This is not a theorem for the selected vector fold specialization or `Vec::extend`. Those implementations, the captured-borrow closure interface, and the complete callback chronology through rho remain open. Privacy and soundness are unproved. Verifier source, CU results and all security parameters are unchanged; no CU or unchanged regression suite was rerun.
