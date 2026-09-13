# Later cached alpha conflict target event

`FSV8AlphaCachedConflictTargetEvent.lean` closes the chronological cached
case needed by the complete-duplex route after at least one pair has run.
When the preceding advance is fresh and the next pair encounters a cached
output or advance, fresh-creator coverage constructs a literal-prefix target
at the preceding advance request.  The result is lifted to the same exact
root `targetEvent`; target membership is not a theorem premise.

The theorem deliberately does not cover a cached lookup in the initial pair,
because there is no preceding alpha advance at which to place this target.
That remains the explicit first-exposure/restoration branch.

Source SHA-256:
`6abe20002b3997d1ea0d7c577f81eec69599b327374e3c264c55ef78654148ed`.

Focused NUC replay used Lean 4.32.0 under a user cgroup with
`MemoryHigh=7500M`, `MemoryMax=8G`, and `MemorySwapMax=0`:

```text
exit: 0
wall: 2.91 s
maximum RSS: 6,803,420 KiB
swap: 0
```

The local creator lemma reports `propext` and `Quot.sound`; the exact-root
theorem reports `propext`, `Classical.choice`, and `Quot.sound`.  No retained
declaration uses `sorryAx` or a custom axiom.
