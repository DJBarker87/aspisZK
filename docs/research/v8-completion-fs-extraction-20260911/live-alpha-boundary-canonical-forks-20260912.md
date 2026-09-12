# Live alpha boundary and canonical programmed outputs

Status: checked deterministic Fiat--Shamir integration milestone.  The global
random-oracle probability lift, complete replay matrix, permitted extraction,
and global soundness theorem remain open.

## What is now constructed

`FSLiveAlphaBoundary.alphaBoundary` computes the exact transcript immediately
before the first alpha candidate from a successful execution of the selected
source-functional middle.  It includes, in order, the inactive claim, nonzero
kappa draw, source-produced public-functional description and claim, compact
profile, nonzero tau draw, response0, and alpha nonce.

`successful_alpha_boundary` proves that the literal `candidateScript` starting
at that constructed boundary returns the successful run's alpha0, has the same
final oracle as the functional candidate, and chronologically queries the exact
`alphaCandidateInput`.  The theorem does not accept an independently supplied
boundary or candidate value.

The matrix collector now preserves a second provenance fact: every selected
checked cell's exact `OriginReplayConfiguration` occurs in the bounded input
configuration prefix.  This proves membership, not that a cell is the intended
canonical `(gamma row, alpha column)` configuration.

`AlphaDigestEncodingProbe` constructs a 32-byte output whose first 16 bytes are
the canonical QM31 representation.  It proves:

- the actual transcript word decoder returns the four canonical limbs;
- those limbs are below the rejection sentinel and are consumed without a
  retry;
- `assemble` reconstructs the exact QM31 value; and
- the literal candidate sampler returns that value whenever its first squeeze
  answer is the constructed output.

`FSV8AlphaProgrammedCandidate` connects this result to an actual projected V7
oracle table lookup.  A table entry at the exact alpha candidate input whose
output is the canonical encoding forces the literal candidate sampler to
return the selected value.  No freshness, distribution, or role-label premise
is used.

## Chronological target partition

`FSV8AlphaTargetDisposition` gives the exhaustive deterministic split at the
alpha candidate input:

1. a matching adversary record is already in frozen q1;
2. the input is already defined in the oracle table; or
3. the input is absent.

Only the first case is passed to the existing start-only replay constructor by
`FSV8AlphaTargetRestorationAdapter`.  The prior-target and absent cases remain
explicit; this work assigns them no probability and does not treat them as
fresh successful programming opportunities.

## Exact remaining seam

The replay constructor operationally programs `forkOutput` at its paused
driving query.  Its exported `IsOperationalCoupling` predicate does not expose
the resulting table-lookup equation.  Therefore the next deterministic bridge
must derive, from `constructLegalReplay = .ok replay`, that the replay's first
post-pause candidate query observes that programmed entry.  That fact can then
feed `projected_lookup_drives_candidate`.

After this bridge, the main structural obligation is still matrix-wide: prove
that the selected 29-by-4 cells are produced from the canonical configurations
and share the required pre-alpha chronology.  Pointwise successful replays and
configuration-list membership do not establish that common history.

## Focused evidence

All runs used Lean 4.32.0, the pinned union cache, `-j1 -M7500`, and zero swap.
They were focused cached compiles, not a clean first-party rebuild.

| Target | Exit | Wall seconds | Peak RSS bytes |
|---|---:|---:|---:|
| `ExtractionCollectorSource.lean` | 0 | 10.97 | 5,618,368,512 |
| `ExtractionCollectorVerifiedMatrix.lean` | 0 | 4.87 | 5,802,901,504 |
| `ExtractionCollectorCanonicalMembershipIntegration.lean` | 0 | 3.37 | 5,826,674,688 |
| `FSLiveAlphaBoundary.lean` | 0 | 3.57 | 5,768,527,872 |
| `AlphaDigestEncodingProbe.lean` | 0 | 11.71 | 5,693,997,056 |
| `FSV8AlphaTargetDisposition.lean` | 0 | 3.46 | 5,795,856,384 |
| `FSV8AlphaTargetRestorationAdapter.lean` | 0 | 3.25 | 5,810,782,208 |
| `FSV8AlphaProgrammedCandidate.lean` | 0 | 12.68 | 5,753,339,904 |

Every printed endpoint uses only `propext`, `Classical.choice`, and
`Quot.sound`; one elementary q1 membership theorem is axiom-free.  A search of
the changed files found no `sorry` and no new `axiom` declaration.

## Security meaning

This closes a real byte-to-field and source-boundary part of adaptive
Fiat--Shamir extraction.  It does not establish the probability of collecting
the fork matrix, the late-target bounds, a checked payment witness, the global
accepted-execution partition, or a numerical global security level.  Grinding
contributes zero bits.
