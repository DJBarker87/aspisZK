# V8 alpha marker origin refinement

## Result

`lean/FSV8AcceptedExactRootAlphaMarkerOrigin.lean` strengthens the accepted
exact-root marker theorem at the actual successful marker query. Every such
execution constructs the literal `queryOracle` success and one of four
alternatives:

1. the alpha candidate input was already in adversary Q1;
2. the marker request was fresh and its answer hit the request target;
3. the marker request was cached and its answer satisfies only the later
   request-level target predicate;
4. the alpha candidate input remained absent at its sampling cut.

The third alternative is intentionally retained. A request-target fact at a
cached replay is not a first-exposure target event.

## Security consequence

This closes an ambiguity in the prior three-way classification, but does not
yet add a probability term. In particular, the following tempting lift is
false without more information:

```text
markerAnswer in operationalRequestTargets at marker replay
  -> exact-root causal target event
```

A legal known-answer chronology can first expose the marker answer, then
create `markerAnswer ++ [1]`, and finally replay the marker input from cache.
The later target predicate is true even though the target did not exist at the
marker answer's first exposure.

The surviving repair route is segment-sensitive. The earlier theorem
`FSV8ProgrammedAlphaFreshDisposition` retains the actual fresh creator of the
candidate in the source or pre-alpha segment. Cached-marker executions must
be analysed at that candidate exposure, with the gamma/kappa/tau dependency
cut appropriate to its segment. They cannot be collapsed into the ordinary
marker target event.

The fresh-marker branch still needs a scheduler-prefix bridge from the nested
one-query `runMachine` to the corresponding exact-root exposure-tree node.
Only after that bridge may its request-target membership be promoted to the
existing `FSV8ExactRootCursor.targetEvent`.

## Focused replay

Base revision: `6f3d2e4f9b4b21fcea62c7b5fc8c320fabef54c2`.

The retained successful run used Lean 4.32.0 on the NUC through Tailscale,
under a systemd service with `MemoryHigh=8G`, `MemoryMax=9G`,
`MemorySwapMax=0`, `RuntimeMaxSec=600`, and Lean flags `-j1 -M8192`.

| Target | Exit | Wall | Peak RSS | Swap | Axioms |
|---|---:|---:|---:|---:|---|
| `FSV8AcceptedExactRootAlphaMarkerOrigin.lean` | 0 | 9.88 s | 6,815,628 KiB | 0 | `propext`, `Classical.choice`, `Quot.sound` |

The first two focused attempts were retained in the system journal as failed
elaboration attempts. They changed no theorem statement; the successful
source has SHA-256
`a9bac62e46e2e6b3cf2673aca186e27fe1bd68ee6c7f9d804ec790f5b8eb519e`.

No literal Rust refinement, probability composition, payment extraction or
global soundness conclusion is claimed by this leaf.
