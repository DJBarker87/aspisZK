# Terminal-parts arithmetic after composition

`TerminalPartsArithmeticExact.run_exact` proves success, canonical output and
the exact formula

```
eqValue(zc, point) * composition + mu * h1
  + (mu * mu) * ((1 - active) * h1).
```

It reuses `EqualityValueLoop.equality_value_success` and the existing selected
QM31 addition, multiplication, subtraction and constant proofs. The point,
zerocheck point and four scalar inputs must be canonical. The actual source
arithmetic operations remain in `run`; they are not replaced by field models.
`check_suffix.py` compares this operation sequence with the retained generated
`terminal_parts` excerpt, allowing only whitespace and the final return binding.

The accepted v2 check exited 0: controller wall 3.036 seconds, peak RSS
3,949,584 KiB, process swaps 0, no watchdog abort. The printed axiom report
contains only `propext`, `Classical.choice` and `Quot.sound`. The exact compiler
time, source baseline `b302c0d49`, command, import pins and resource reservation
are recorded in the accepted receipt. Rejected import-order and alias-rewrite
attempts are retained separately; their error-generated `sorryAx` reports are
not accepted evidence. The successful environment selects the complete project
overlay and complete Mathlib roots before partial namespace overlays.

This theorem covers the arithmetic suffix after composition succeeds. It does
not yet connect the composition caller, the public wrapper or the opaque
`FinishModel.terminal` boundary to this suffix. It does not establish complete
100-bit soundness or source equivalence of the whole generated artifact.
