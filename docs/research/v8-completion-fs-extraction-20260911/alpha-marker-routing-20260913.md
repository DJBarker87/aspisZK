# Accepted exact-root alpha marker routing — 2026-09-13

## Result

`FSV8AcceptedExactRootAlphaMarkerDisposition.lean` now constructs, from one
accepted exact-root execution and its one submitted body, a three-way causal
classification for the first alpha candidate input:

1. the exact `digest ++ [1]` input already occurs in adversary Q1;
2. the answer returned by the actual alpha marker belongs to the marker
   request's operational target set because an earlier verifier query created
   that candidate coordinate; or
3. the candidate input is absent at the candidate sampling cut.

The earlier four-way origin theorem distinguished source insertion and
pre-alpha insertion.  The new proof routes both through the literal marker.
For the pre-alpha case it proves that the complete pre-alpha final oracle is
the factored marker-continuation oracle, exposes the marker as exactly one
`queryOracle` call, proves its tagged input differs from `digest ++ [1]`, and
moves the candidate lookup backward across that query.  Initial absence and
the before-marker lookup then construct an actual fresh creator record in the
chronological `historySince` segment.  No phase label is accepted as evidence.

This is deterministic request-level routing.  It does **not** yet prove that a
request target is an exact-root target event, that the absent branch realizes
all eight fresh alpha coordinates, that restoration succeeds, or that any
probability term applies.

## Focused proof evidence

The new endpoint and its two immediate operational leaves were replayed on the
Tailscale NUC with Lean 4.32.0, `-j1 -M8192`, `MemoryHigh=8G`,
`MemoryMax=9G`, `MemorySwapMax=0`, and a 600-second runtime cap:

| Leaf | Exit | Wall | Peak RSS | Swap |
|---|---:|---:|---:|---:|
| `FSV8ProgrammedAlphaMarkerQuery.lean` | 0 | 3.12 s | 6,750,016 KiB | 0 |
| `FSV8ProgrammedAlphaPreMarkerTarget.lean` | 0 | 6.94 s | 6,759,972 KiB | 0 |
| `FSV8AcceptedExactRootAlphaMarkerDisposition.lean` | 0 | 11.89 s | 6,786,828 KiB | 0 |

`#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.
The machine-readable receipt records hashes for these leaves and the seven
direct supporting leaves.

## Hostile review findings retained

The new theorem does not use `rootToAlphaForkCursor`, and hostile review found
that the older object is not yet a valid pre-alpha restoration producer: it
starts verifier replay from the adversary's completed oracle, which may already
contain alpha or later queries, and its `.forkPair` emission does not establish
missing/distinct inputs or successful programming.  Its coordinate theorem is
only tape plumbing.  This older fork route is therefore **rejected as a causal
restoration endpoint** until replaced by a cursor rooted at the real cut.

A hostile subreview initially reported that `StrongCausalAlphaDisposition`
carried labels without provenance, but it had inspected the sibling checkout
rather than this worktree.  Direct inspection here falsified that finding: the
current constructors do carry segment-local `historySince`, actor, input and
output facts.  The promoted endpoint is stronger still:
`source_runs_construct_fresh_disposition` reconstructs fresh records from
actual lookup transitions, and the marker-routing theorem consumes those
records.  The generic two-segment lookup lemma remains retrospective and is not
used by itself as a probability premise.

## Next exact gate

Lift `AlphaMarkerDisposition.markerTarget` into the existing exact-root target
event using the actual request and root chronology, and couple
`freshAtCandidate` to the complete one-to-four-pair alpha sampler.  The
adversary-Q1 branch must use a restoration cursor rooted at the real pre-alpha
cut, not the rejected post-adversary-completion cursor.

Only after those three branches have executable producers can the alpha term
enter the adaptive Fiat–Shamir ledger.
