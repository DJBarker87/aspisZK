# S1 fresh-cut source connection

Date: 2026-09-13

Branch: `research/v8-completion-fs-extraction-20260911`

Base inspected: `9d644fa0087bcfcc626fa0e588b34abba9aea67f`

## Result

This continuation closes a real source-to-root boundary for **genuinely fresh
requests**.  Given a returned V8 functional execution and a positional member
of its verifier `freshQueries`, Lean now constructs:

1. the request's exact position in the actual `runExactRoot` trace;
2. the exact global scheduler-native request at the root cursor after the
   adversary answers and preceding verifier answers;
3. the request state and preceding-verifier-query history facts; and
4. inclusion of a literal operational target hit at that request in the
   existing exact-root target event.

The resulting event is bounded by `exactCompilerExactCountError`.  This is the
same root event already present in the compiler accounting, so there is no
per-request union and no grinding/work term.

The promoted endpoint is
`returned_verifier_fresh_target_hit_mem_exact_root_event` in
`FSV8ReturnedVerifierFreshTargetEvent.lean`.  Its only target-specific premise
is that the answer belongs to `operationalRequestTargets` of the exact request
state constructed at that positional source cut.  The request, trace and state
are not caller-supplied coherence certificates.

For the source route that retains a concrete earlier creator record, the
marker-specific transport is also closed when that creator has
`actor=.verifier` and `origin=.fresh`: the exact marker split places the
creator among the preceding queries, the global request retains it, and its
literal-prefix relation is charged to the same root target event.  No equality
between the local marker state and global request state is assumed.

The accepted-run wrapper now preserves and consumes that provenance before it
can be erased.  `returned_accepted_exact_root_routes_alpha_marker_target_event`
constructs one exhaustive source disposition from the same returned and
accepted execution:

1. prior adversary candidate input;
2. a genuinely fresh marker whose source/pre-alpha fresh verifier creator is
   charged to the existing exact-root target event;
3. cached marker reuse from a fresh table entry, retaining target membership
   and output equality;
4. cached marker reuse from a programmed table entry, retaining the same
   evidence; or
5. candidate input absent at the candidate cut.

Thus the earlier `accepted_origin_retains_creator_provenance` obligation is
closed for the two verifier-insertion/fresh-marker branches.  The cached
marker branch remains explicit and uncharged; this classifier is not an
ordinary-alpha sampler law.

Separately, `AlignedSqueezePair.initialDisposition` gives the exact three-way
split at the state before either call of one real aligned squeeze pair:

- output and advance both fresh and initially absent;
- output fresh/initially absent, advance cached at the initial state; or
- output cached at the initial state.

The proof transports the advance lookup back across the distinct fresh output
insertion.  It assigns no probability and currently covers one aligned pair,
not the complete four-pair ordinary sampler.

Cached or programmed creator records are deliberately not promoted.  A cache
hit emits no `machineFresh` record and requires first-producer provenance.

## Checked leaves

All retained leaves compile with Lean 4.32.0.  Their promoted declarations use
only `propext`, `Classical.choice`, and `Quot.sound` (some individual helper
declarations use a subset).

| Leaf | Security/source meaning | Status |
|---|---|---|
| `FSV8ProgrammedAlphaMarkerHistoryPrefix` | Same source marker continuation reaches the same factored verifier history | PASS |
| `FSV8OutsideTargetTraceClean` | Operational reindexing preserves the actual V8 root trace; outside target event it is chronologically clean | PASS |
| `FSV8MarkerFreshVerifierQueryBridge` | A successful missing marker query appends its literal fresh record | PASS |
| `FSV8MarkerFreshVerifierMembership` | That marker pair belongs to the same returned verifier `freshQueries` | PASS |
| `FSV8FreshRequestTargetEvent` | Actual fresh request target hit is included in the exact-root target event and inherits its exact count bound | PASS |
| `FSV8ReturnedRootFreshTracePrefix` | Returned projected adversary/verifier records form a prefix of the actual root trace; a verifier member has a trace coordinate | PASS |
| `FSV8RootVerifierNativeRequest` | A verifier member constructs the exact global native request and retains prior-query history | PASS |
| `FSV8ReturnedVerifierFreshTargetEvent` | Joins the trace, request, and target-event inclusion on one returned execution | PASS |
| `FSV8MarkerFreshEnumerationSplit` | Exact preceding fresh-query list at the marker and fresh-creator retention at the global request | PASS |
| `FSV8MarkerFreshCreatorTargetEvent` | Fresh verifier creator at the marker is charged to the exact-root target event | PASS |
| `FSV8MarkerFreshTargetReduction` | Arbitrary marker target is charged or exposes a concrete missing prior record | PASS |
| `FSV8OperationalTargetMonotone` | Operational targets persist under chronological history extension | PASS |
| `FSV8MarkerFreshVerifierCut` | Same-run fresh marker constructs the exact entry/append/final history cut | PASS |
| `FSV8PreAlphaMarkerCreator` | Pre-alpha insertion retains the actual before-marker fresh creator | PASS |
| `FSV8AcceptedExactRootAlphaMarkerTargetEvent` | Accepted execution preserves fresh creator provenance and routes its fresh-marker branch to the existing root event while retaining cached/adversary/absent alternatives | PASS |
| `FSV8AlignedAlphaInitialPairDisposition` | One actual aligned output/advance pair is classified at its common initial state | PASS |
| `FSV8AlphaTotalSuccessfulCoordinates` | Successful eight-coordinate V8 alpha tape is equivalent to the existing successful Tag-73 raw stream with all four advance digests preserved | PASS |
| `FSV8SourceBufferedDecode` | Pinned source decoder consumes literal sentinel/canonical first-block patterns and rejects the all-sentinel block | PASS (deterministic) |
| `FSV8ExactRejectionWeights` | Exact bounded-geometric and fixed-tuple mass identities, including the V8 `n=2^31`, cap-eight instance | PASS (ideal arithmetic) |

Focused NUC compilation used systemd scopes with `MemoryHigh=7500M`,
`MemoryMax=8G`, and `MemorySwapMax=0`.  The final three runs were:

| Target | Exit | Wall | Peak RSS | Swap |
|---|---:|---:|---:|---:|
| `FSV8ReturnedRootFreshTracePrefix.lean` | 0 | 2.69 s | 6,765,448 KiB | 0 |
| `FSV8RootVerifierNativeRequest.lean` | 0 | 2.82 s | 6,828,692 KiB | 0 |
| `FSV8ReturnedVerifierFreshTargetEvent.lean` | 0 | 2.84 s | 6,827,416 KiB | 0 |
| `FSV8MarkerFreshEnumerationSplit.lean` | 0 | 2.79 s | 6,806,952 KiB | 0 |
| `FSV8MarkerFreshCreatorTargetEvent.lean` | 0 | 2.85 s | 6,831,952 KiB | 0 |
| `FSV8MarkerFreshTargetReduction.lean` | 0 | 2.88 s | 6,828,428 KiB | 0 |
| `FSV8OperationalTargetMonotone.lean` | 0 | 2.64 s | 6,789,056 KiB | 0 |

The first trace-prefix attempt failed on list association and was replaced by
an explicit rewrite; it was not rerun with a larger memory cap.

## Exact probability scope

Let

- `F = unifiedFull256ExposureCap parameters`,
- `G = globalFull256OracleCallCap parameters`, and
- `C = choose(F,2) + F*(G+1)`.

The reused exact-root bound is

`exactCompilerExactCountError = C * (2^256)^(F-1) / (2^256)^F`.

The new theorem proves event inclusion into that exact event.  It does not
assert an independent local random-oracle law and therefore does not
double-charge `C / 2^256`.

The complete-duplex ordinary sampler claims supplied in the standalone prompt
remain **not source-connected here**:

- fresh output and fresh advance;
- fresh output with cached advance; and
- cached output.

The ideal formula `s / p^4`, with `s=(1-(2^31)^-8)^4` and
`p=2^31-1`, has not been promoted as the distribution of the actual V8 cut.
The referenced sampler certificate and Lean/Rust drafts were absent from the
available download.

The first-block fallback is **not used**.  Its charge would be
`J * 56 / 2^155`, but there is no proved V8 invocation/site/fork cap `J` in
this checkout.  Neither the V7-specific 1511 cap nor `29*4` was substituted.

## Compatibility and remaining boundary

No protocol, parser, transcript, field, query count, verifier acceptance rule,
or proof format changed.  The body remains exactly

`697*16 + 52 + 24 + 22*621 + 2*296*26 = 40,282 bytes`.

The status is:

- **PASS:** same-root fresh-request target-event probability bridge;
- **PASS:** marker-specific transport for a retained fresh verifier creator;
- **PASS:** accepted-run classifier retains the source/pre-alpha fresh creator
  until its fresh-marker branch is charged to the root target event;
- **PASS:** source-exact initial-state disposition for one aligned squeeze pair;
- **PASS:** deterministic successful-tape equivalence required by the existing
  complete causal ordinary-probability consumer;
- **PASS:** literal first-block decoder behavior and exact complete ideal
  decoder mass identities;
- **OPEN:** complete-duplex actual sampler law and both cached cases;
- **NOT USED:** first-block fallback;
- **NO CLAIM:** global 100-bit soundness, allowed-access extraction, adaptive
  zero knowledge, literal Rust refinement, or complete-transaction CU parity.

The next exact source obligation is to lift the one-pair initial disposition
through all four sequential alpha squeeze pairs and attach the complete
source decoder law on the all-fresh coordinates.  The output-fresh/
advance-cached and output-cached alternatives, including the explicit cached
marker branch above, must trace to their actual first exposure and remain
separate until charged.  No current theorem establishes the ideal fixed-alpha
mass for the actual source execution.  Assuming independence from labels,
treating cached calls as fresh, or composing four isolated marginal laws would
not close this obligation.
