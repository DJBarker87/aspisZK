# R174 selected gamma-batch closure step

`R174GammaBatchStep.rawCallMut` retains the selected extracted mutable-power closure body. The [evidence manifest](evidence/r174-gamma-batch-step/manifest.json) checks it against the pinned full extraction, with only explicit namespace qualification normalization and the declaration rename. The returned backward function is retained and applied.

`rawCallMut_closed` proves the exact raw operation order: multiply power by value, add to accumulator, multiply power by gamma, then close the returned borrow. Every arithmetic failure and divergence is preserved. `encoded_closed` uses the selected field execution theorems to prove the output is accumulator + power*value and the captured next power is power*gamma. Both compiled in the pinned capped cache, 1.56 seconds, peak RSS 3,712,992 KiB, zero swaps. Their complete axiom reports contain only propext, Classical.choice and Quot.sound.

The first compile found a missing existing `MaskClosureWriteback.olean`; the evidence retains that failure and focused materialization of that dependency. No unchanged regression suite was run. The verifier source and all security parameters are unchanged.

This proves the extracted closure step, not the complete source fold. Actual standard-library slice fold/Vec extend, full freeze execution, justification of the chord inverse, and callback/oracle chronology through rho remain open. No whole trace equality, privacy or soundness claim is made.
