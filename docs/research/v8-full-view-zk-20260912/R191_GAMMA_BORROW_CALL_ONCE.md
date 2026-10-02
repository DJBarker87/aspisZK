# R191 gamma owned-call borrow closure

The actual source-shaped gamma `call_once` wrapper equals `finishCall` of its raw `call_mut` for every input. The proof preserves failure and divergence, applies the returned backward function, and retains both the updated power and fixed gamma. On canonical encoded field values it produces the exact weighted accumulator and next power proved in R174.

The staged raw body agrees with the saved generated body after mapping the already-proved raw callback name and local argument name. This result does not make the mismatched generated dictionary a well-typed builtin `FnMut` instance or prove the selected slice implementation.

The focused target compiled on the pinned capped Lean 4.32 workspace: exit 0, 1.48 seconds, peak RSS 3,713,216 KiB, zero swaps. Both complete axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`. See the [evidence manifest](evidence/r191-gamma-borrow-call-once/manifest.json).

Next: faithful typed captured-borrow and selected slice/Vec extension correspondence, then complete callback chronology through rho including every failure and oracle call. End-to-end privacy and soundness remain unproved. Verifier source, genuine CU results and all parameters are unchanged; no benchmark or unchanged regression was rerun.
