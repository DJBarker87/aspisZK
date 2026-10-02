# R193 counted slice-fold control model

R193 proves a Nat-indexed counted-loop control model equals the R183 monadic list fold, assuming each in-range load succeeds with the corresponding list element. The theorem keeps callback failure and divergence, follows the callback environment through each step, handles the final stop, and discards the final environment in the fold result.

The focused target compiled in the pinned capped Lean 4.32 workspace: exit 0, 1.24 seconds, peak RSS 2,539,676 KiB, zero swaps. Its complete axiom report lists only `propext`, `Classical.choice`, and `Quot.sound`. The source, three failed drafts, complete logs, and R160 source inventory are retained in the [evidence bundle](evidence/r193-counted-slice-fold-control/manifest.json).

The remaining first proposition is to show that the selected source pointer reads, length and empty tests, and unchecked `usize` increment implement this Nat-indexed control model. The captured-borrow selected fold and `Vec::extend` chronology also remain open. R193 proves no pointer or `usize` refinement, actual-slice override correspondence, full freeze equality, privacy, or soundness.
