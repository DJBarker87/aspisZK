# Alpha candidate suffix synchronization

## Result

The retained leaves establish two deterministic links for the same accepted
alpha candidate execution:

- projection equality carries the accepted final pair's fresh advance into
  the candidate terminal history with the exact input, output and fresh
  origin;
- cancellation of the common entry-history projection places a matching
  literal record in the records appended by the candidate source machine.
  The source machine supplies verifier actor provenance, rather than deriving
  it from the actor-erasing projection.

The second leaf also proves that such an appended fresh record remains in the
fresh-query enumeration of an enclosing whole-verifier history when the two
literal chronological prefix facts are supplied.

These are source-history facts, not yet the complete accepted-run inclusion in
the routed ordinary-alpha event.  In particular, the retained main theorem
currently treats the successful final pair's advance; the other consumed
pair coordinates and cached-origin alternatives remain in the next bridge.

## Sources

- `FSV8AlignedAlphaCandidateProjectionSync.lean`
  SHA-256 `ab5ad0dbd568a902dd52e3f728acff39d5f8f8923b7e397799c12ff2db9959ed`
- `FSV8AlignedAlphaCandidateSuffixSync.lean`
  SHA-256 `5b334589bbac32f2d374e50d9737b5744e16638c2bfeff79d6e03fe72e66e393`

Base revision before these leaves:
`3e2a3a845e24d3253e4635d4056cdcb6e8e9dbbf`.

## Focused pinned replay

The suffix leaf was replayed on the NUC through Tailscale with Lean 4.32.0 in
a user cgroup (`MemoryHigh=7500M`, `MemoryMax=8G`, `MemorySwapMax=0`):

```text
exit: 0
wall: 2.95 s
user: 2.07 s
system: 0.89 s
maximum RSS: 6,820,040 KiB
swap: 0
```

The earlier focused replay of the projection leaf used the same pinned
environment:

```text
exit: 0
wall: 2.83 s
maximum RSS: 6,796,840 KiB
swap: 0
```

## Axiom audit

The promoted declarations use only the accepted foundations among
`propext`, `Classical.choice`, and `Quot.sound`.  Neither source contains
`sorry` or a custom axiom.
