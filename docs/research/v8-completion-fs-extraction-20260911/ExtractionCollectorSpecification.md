# Bounded 29×4 collector: operational specification

2026-09-12. Source review only unless a later focused receipt explicitly
upgrades the new interface. No probability statement or successful-fork
assumption. Existing checked batch files are unchanged.

## Retained minimal interface

`lean/ExtractionCollectorInterface.lean` imports only the exact existing
`AspisFormal.K1.V7FsStateRestorationCoupling`. Its `attempt` calls
`constructLegalReplay` using the capability, initial oracle, first run and
observation from ONE `SameTapeExperimentOrigin`. It retains replay failures
and separately evaluates `check output.returned`; rejection is not discarded.
`attempt_success` derives a genuine operational replay and that actual
checker equation. `attempts` retains every outcome, while `checkedRecords`
is just the checked projection; its count is bounded by the declared attempt
budget. `required_matrix_size` proves the shape count 116, not existence.

The result checker is still an explicit function argument. No theorem says
an arbitrary instantiation checks V8 acceptance. The interface is not a
complete nested scheduler, V8 source refinement, or executable minority
decoder. In particular, the generic one-driving-query constructor is not
silently identified with programming both halves of a V8 squeeze.

Historical import pin, also matching current local source:

```text
V7FsStateRestorationCoupling.lean
808268dd37cab2becb9f72f46b4d81ebfdf872d51b3503dd7711b9cecb45de5b
V7FsStateRestorationCoupling.olean
035723c78d1fd8a35aa9220f15c1e85d7fa80ec0aa424109796751369f11c9d2
```

These are from `results/.../opened-update-v4/report.json`: retained historical
4.32 imports, not a fresh patched-source rebuild. The larger
`V7Tag73ConcreteRestorationClient` is not registered in that receipt; this
audit neither installed it nor inferred cache compatibility.

## Exact V7 reuse, and its limits

| Source/declaration | What can be reused |
| --- | --- |
| `V7FsStateRestorationCoupling.makeSameTapeExperimentOrigin` | First execution and opaque start-only capability share the same hidden tape; the extractor does not receive that tape or an arbitrary checkpoint. |
| `.constructLegalReplay`, `.map_from_origin_success_preserves_identity_q1_pause_history_resources` | Prefix replay, derived pause, actual returned result, preserved histories and resource checks; explicit prefix/programming/budget/timeout failure. Not acceptance. |
| `V7Tag73FullFromStartRestoration.constructFullFromStartReturnedReplay` | Pair programming at the literal ancestor prefix and restart from the original source closure; successful replay becomes another scan-capable node. |
| `V7Tag73ConcreteRestorationClient.ConcreteRestorationRequest` | Runtime request is `(nodeId, verifierTransitionIndex)`, not a caller-supplied state or SHA input. |
| `.dispatchPreparedRestoration`, `.start_concrete_restoration_client_from_root_dependent_induction` | Actual dispatcher and induction over fuel-bounded adaptive requests, with all replies/failures and append-only costs. `.added` means the stages returned, not verifier acceptance. |
| `V7Tag73UniqueRestorationRequests.appended_child_preserves_root_request_preparation` | A new child does not mutate an ancestor; repeating root requests is allowed. Request uniqueness would wrongly forbid ordinary multiple-response extraction. |
| `.node_local_no_pair_conflict_is_ancestor_entry` | Absence in the current segment does not imply fresh inputs: a pair input may already be defined in the ancestor table. |
| `V7Tag73AtomicForkUniformScheduler.run_unified_exposure_schedule_direct_fork_exactly_two` | Atomic output/advance scheduling uses two full256 coordinates. The scheduling/count structure is reusable; its old concrete probability bound is not instantiated here. |
| New `FSOracleExecution.call_bound`, `.retained_prefix`, `.run_preserves_answer` | Bounded actual V8 byte-oracle scripts preserve logs and cached answers, including aborts. No restarting or programming operation is thereby authorized or implemented. |

Old concrete restoration nodes use Tag73's `FutureFreeVerifierState`, source
messages and transition schedule. V8 must construct its own source-state
map/dispatcher with the same operational discipline. The old verifier-call
constants (for example 1511/1979) and old event/probability envelopes cannot
be copied into V8 resource or soundness claims.

## Concrete collector policy

Input: the actual first-run origin, one fixed pre-gamma ancestor, finite
outer-attempt budget R, additional-alpha budget b per usable outer node,
global oracle/exposure/time limits, and the actual source-result checker.
No pStar, full encoded word, desired candidate list or successful-fork oracle.

For each of at most R outer attempts:

1. Request gamma restoration from the SAME immutable completed-OOD ancestor.
   Retain failure, abort and all costs. A returned node must pass the actual
   source verifier/parser and fixed-prefix checks; `.added` is insufficient.
2. Its actual gamma and alpha0 labels and final256 seed one row. If gamma
   duplicates an already completed row, skip it. Locate the actual pre-alpha
   ancestor in this returned node; do not synthesize a checkpoint.
3. Make at most b further alpha restorations from that one immutable parent.
   Keep the first four distinct alpha labels passing the same source checks,
   including the seed. Failures, duplicate labels and rejected results consume
   budget. An incomplete row is not a four-response row.
4. Stop at 29 completed rows, or return the incomplete table plus the exact
   failure/charge ledger when the bounds are exhausted.

This policy is executable in terms of concrete restoration replies and
public source checks. It does NOT test noncomputable `RecoveredHigh`,
`RecoveredMiddleFork`, support, or mathematical family membership.

## Minimal per-prefix conditions and honest theorem skeleton

Operational conditions are SAME hidden-tape origin and ancestor provenance;
literal source transition location; coherent oracle/prefix; actual output
and advance input framing; legal programming only in the restored base;
source checks for every counted result; distinct decoded labels; and recorded
costs within the chosen limits. Replay conflicts/prequeries/retries remain
failure data, not assumptions of probability zero. Four alpha nodes share
gamma, inactive, kappa, tau and response0. All gamma rows share C1,
lambda/chi, C2, theta/z/mu, eta, ten semantic rounds, claims, semantic check
and both OOD answers. Final/query/rho/later responses remain adaptive.

No lower success rate is needed for the following unconditional output form:

```text
collect29x4(origin,R,b,limits,sourceCheck)
  returns either Incomplete(table,failures,costs)
  or Complete(matrix,failures,costs).

Complete ⇒ 29 distinct gamma rows, 4 distinct alpha nodes per row,
            each node actually returned by a permitted replay and passed
            the actual checker; all costs satisfy the derived bounds.
```

For completeness there is one necessary **progress event**, not a proven
success assumption: within the realized R attempts, 29 distinct outer rows
each obtain three further distinct checker-accepted alpha continuations in
their b attempts before limits stop the computation. The deterministic
theorem `progress → Complete` is useful; it gives no probability of progress.
Any eventual probabilistic premise must hold for each reachable full history
and the relevant immutable prefix, not just the initial run's marginal
acceptance rate. The existing files do not supply such a premise.

For a complete matrix define, with precedence, these uncharged events:

```text
sourceMismatch;
else some selected continuation is not RecoveredHigh;
else some selected continuation has its actual high Q support >252847;
else the matrix is a RecoveredMiddleFork matrix.
```

The current `RecoveredHighForkExtraction.recovered_components_family_facts`
consumes the LAST case and the SAME fixed family.card≤1; it constructs family
membership, own support≥38228 and early-family membership of the final-only
reconstruction. Its upper middle bound must remain visible. To consume all
RecoveredHigh nodes instead, use `high_support_unique` and the generic
`SelectedMiddleFourAlpha.Generic.reconstruct_folds`; that stronger adapter
is not asserted by the existing middle-only theorem. Family membership is
derived after a good matrix, never supplied to the collector as input.

The remaining source/collector theorem therefore has the honest form

```text
not Incomplete ∧ no sourceMismatch ∧ no selected non-recovered/non-middle node
  → computed tuple has the actual recovered-family facts.
```

All excluded events require a separate justified analysis. No term is
assigned a probability in this specification, and no failure branch is
eliminated by choosing successful histories after the fact.

## Exact resource envelope

Let `B = R*(1+b)`. The policy performs at most B restoration requests: R outer
replays and at most R*b additional alpha replays. To fit a matrix, necessarily
R≥29 and b≥3. At those minimal shape budgets B=116. These are capacities,
not a claim that 116 attempts suffice. The original first run is additional;
this conservative policy does not count it as a matrix node.

The actual V7 dispatcher may invoke the closed prover start twice per
request: a prefix reconstruction and a full-from-start replay. Thus:

```text
restoration requests                         ≤ B
closed prover starts after the first run      ≤ 2B
added returned nodes                         ≤ B
uniform atomic fork coordinates              ≤ 2B
successfully programmed points               ≤ 2B

Q = Qinitial + Σj (Qprefix,j + Qrestart,j + Qverify,j)
  ≤ Qinitial + B*(qPrefix + qRestart + qVerify)
F ≤ Qfresh + 2B
T ≤ Tinitial + B*(tPrefix + tRestart + tVerify + tDispatch) + tInterpolation.
```

The query sum includes failures and cache hits when an oracle call occurs.
Programming coordinates, fresh answers and oracle calls are different
counters; do not add one under several labels. The cap bounds require each
corresponding per-request cap to be enforced and recorded. Counting only
successful `.added` nodes is unsound. Initial resource use must be counted
once: the generic coupled replay's `resources` includes first-run use, so
summing those totals over attempts would incorrectly multiply that base.

For B=116, at most232 post-first-run start invocations and232 atomic
coordinates/programmed points fit the envelope; the minimum good matrix
contains116 continuations and29696 final field elements (475136 actual
16-byte source encoding bytes), plus all proof/log/framing data. Total oracle
calls and runtime remain the displayed symbolic quantities until the actual
V8 script, adversary and verifier caps are provided. There is no grinding
credit or generic Fiat–Shamir multiplier.
