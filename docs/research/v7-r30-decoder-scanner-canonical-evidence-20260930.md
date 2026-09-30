# V7 production decoder scanner canonicality

Source parent: `c8f7928dd` (`formal: prove callback prepared field operations`).
Checked source SHA-256: `e005f4452277895bd694d1ebb9061bfcd6c681bdbbce7bb36262b66245840320`.

Focused target: `V7ProductionCallbacksR30DecoderCanonical.lean`, compiled with
`lake env lean -j1` using the pinned Lean 4.32.0 backend and the existing R26/R29/R30
compiled cache on `dombarker@100.108.41.90`.
Command wrapper: `toolchain/check-r30-decoder-focused.sh` in the source bundle.
Scope: `run-r0681aa35d3ad4e4aa2c9373ac7821331.scope`;
`MemoryHigh=7G`, `MemoryMax=8G`, `MemorySwapMax=0`.
No other build scope was active at preflight; host available RAM was 49 GiB.

Result: exit **0**, wall **2.06 s**, peak RSS **2,691,060 KiB**, swaps **0**.
`#print axioms successful_scanner_zero_canonical`:
`[propext, Classical.choice, Quot.sound]`.

The theorem follows a finite exact trace of the production callback's inner
scanner. A zero final invalid flag implies a zero initial flag and canonicality
of every word at or after the initial iterator position. Each OR edge uses
symbolic `Nat.left_le_or` / `Nat.right_le_or`; the proof does not evaluate a
concrete packed byte sequence or unroll a fixed limb count.

Focused development failures were local theorem errors, not memory failures:
the initial wrapper needed an explicit Lean source root; the Boolean conversion
needed its propositional comparison; and iterator indexing needed the
`List.Inhabited_getElem_eq_getElem!` bridge. All were corrected before the final
focused result. No full manifest or unrelated runtime regression was run.

This increment closes only the inner scanner. Outer packed decoder output,
gamma-combined query values, fold polynomial, and the R26 terminal
`runningCanonical` premise remain open. Historical V7 gamma-prefix proofs and V8
research do not establish this missing end-to-end V7 arithmetic chain.
