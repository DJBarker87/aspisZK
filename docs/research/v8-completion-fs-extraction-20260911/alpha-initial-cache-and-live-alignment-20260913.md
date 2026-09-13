# Alpha initial-cache and live-alignment checkpoint

Date: 2026-09-13

Branch: `research/v8-completion-fs-extraction-20260911`

## Result

Two source boundaries are now explicit.

First, the initial alpha pair cannot be charged by the theorem for a cached
conflict after an earlier alpha advance.  If the output is fresh and the
advance is cached, the source constructs the actual fresh creator of the
cached advance key.  Turning the fresh output answer into a literal target for
that key would additionally require equality between that answer and the
prior digest; this equality is not supplied by the source disposition.  If the
initial output is cached, the exact marker classifier reduces it to prior
adversary, the already charged root target, or cached-marker provenance.  The
restoration/first-block alternatives therefore remain explicit.

Second, the live functional alpha run can be composed from a literal returned
candidate and source-constructed initial/final state alignments.  The new
composition constructs `SuccessfulAlignedChallenge` and preserves terminal
alignment.  It does not assume challenge success, but it still takes the
source phase/capacity facts `NoProgrammed`, `RejectedCandidatePrefix`, total
room, fresh room and tape room.  Producing those facts from the complete
accepted root is the remaining constructor boundary.

An attempted single theorem whose result type repeatedly unfolded the entire
nested pre-alpha source execution hit the deterministic 600,000-heartbeat
limit.  It was not retained or retried with a larger limit.  The successful
proof was decomposed into the small composition above.

## Focused Lean 4.32 replays

All commands ran on the NUC in a user systemd scope with
`MemoryHigh=7500M`, `MemoryMax=8G` and `MemorySwapMax=0`.

| Leaf | Exit | Wall | Peak RSS | Swap | Axioms |
|---|---:|---:|---:|---:|---|
| `FSV8AlphaInitialCachedCases.lean` | 0 | 2.85 s | 6,801,116 KiB | 0 | `propext`, `Classical.choice`, `Quot.sound` (subsets on two lemmas) |
| `FSV8ProgrammedAlphaCandidateAlignment.lean` | 0 | 2.73 s | 6,733,464 KiB | 0 | `propext`, `Classical.choice`, `Quot.sound` |
| `FSV8ProgrammedAlphaLiveAlignmentComposition.lean` | 0 | 2.65 s | 6,769,332 KiB | 0 | `propext`, `Classical.choice`, `Quot.sound` |

No `sorry`, custom axiom, protocol change, proof-format change or probability
claim is introduced by these leaves.

## Security implication

The later cached-conflict branch remains charged to the existing exact root
target event.  This checkpoint does **not** charge the two initial cached
branches, prove the complete ordinary-alpha sampler law, or establish global
V8 soundness.  It prevents those cases from being hidden behind an invalid
freshness or digest-fixed-point assumption.
