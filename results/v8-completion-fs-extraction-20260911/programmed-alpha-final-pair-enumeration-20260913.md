# Programmed alpha final-pair enumeration bridge

The source-shaped composition in
`FSV8ProgrammedAlphaFinalPairFreshEnumeration.lean` places a fresh accepted
alpha final-pair advance in the literal fresh-query enumeration of the same
factored whole-verifier run.  Candidate-to-whole history nesting is produced
from the programmed cut; it is not a caller-supplied interval.

This is an intermediate deterministic bridge.  It covers the final fresh
advance, not cached alternatives or the complete routed-event inclusion.

Source SHA-256:
`ec5897b29e1d7579a10eda072fc752ad374636c8b215026b84dcafcbfabff563`.

Focused replay on the Tailscale NUC used pinned Lean 4.32.0 and a user cgroup
with `MemoryHigh=7500M`, `MemoryMax=8G`, and `MemorySwapMax=0`:

```text
exit: 0
wall: 3.30 s
user: 2.19 s
system: 1.10 s
maximum RSS: 6,800,480 KiB
swap: 0
```

The promoted theorem reports only `propext`, `Classical.choice`, and
`Quot.sound`.  The retained source has no `sorry` or custom axiom.
