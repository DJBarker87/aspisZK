# Witness-independence investigation

The exact condition is `PV_OptB_Factorization.Independent`: for two admitted
witnesses with equal public input, at the **same** OS world and coins, the
reached failure observation (`none` or a call family/position/error) agrees.
A generic public-signal experiment proves no such source fact by itself.

The imported first-draw theorem is useful but insufficient. It fixes a
successful first account callback, a nonzero nonce and a fault on the first
entropy draw. It proves identical execution and complete decoded views for
arbitrary witnesses, because neither body executes.

Later calls are reached only when `prove_masked_attempt` returns `Rejected`.
The full emitted `prover.retry_attempt` immediately recurses on that case,
returns on a successful proof, and returns on all other errors. The effect
interpreter likewise calls the emitted body literally and retains the same
OS tape, policy and store across rejection. Thus a witness-independent tape
of *potential* faults is not yet a witness-independent **reached** fault.

A raw-caller native probe is being used to check this distinction without
changing shipped code. Its malformed compilation branch is explicitly not
a pair of admitted `BuilderCanonical.Instance` witnesses. Such a result
cannot be advertised as the D215 honest-witness counterexample, nor used to
claim that option A has been proved necessary for that headline.

No new trust item is introduced. The remaining P obligation must address
reachability, not merely the distribution of each OS reply once requested.

## Checked results so far

- `PV_OptB_SourceFirstFailure.first_callback_error` proves the full emitted
  caller stops on its first callback Entropy error. Its observation theorem
  quantifies over every function of the complete returned source result.
- `PV_OptB_RetryControl.fixed_potential_fault_is_insufficient` is a closed
  model/control counterexample using the existing eight-attempt recurrence.
  It does not instantiate the emitted proof body or admitted witnesses.
- Native programmed-oracle probe: same public digest
  `63088d54be2bed7df9e21bd80e5798dac81821370939da17542242b0be82cbd9`, same
  deterministic first 64 bytes and second-draw EIO schedule. Malformed private
  compilation: one callback, Semantic, no EIO reached. Fixture compilation:
  two callbacks, EIO at zero-based draw position 1, Entropy. The oracle is one
  fixed public HashFn argument returning zero only at the transcript squeeze
  call shape; the default HOST_HASH probe did not produce a counterexample.
  **Not a D215 admitted-witness counterexample**: one compilation is malformed,
  and the programmable oracle is not the fixed native HOST_HASH function.
- `PV_OptB_WitnessFamily.rspendPlus` proves that sixteen private path
  coordinates may vary, with only the public anchor updated, preserving the
  spend relation. This is a route to a pair of admitted witnesses at a common
  root; no such pair with differing reached failures is claimed yet.
- `PV_OptB_Pigeonhole.distinct_small_sets` proves the finite-cardinality
  obstruction needed for a possible distinct-pole-set construction. No native
  trace or failure-reachability consequence is inferred from it alone.

Full reached-failure independence for admitted deployed witnesses remains
OPEN. No premise has been removed, no trust item added, and option A has not
been inferred from these narrower examples. Stage 3 remains conditional on
settling this source obligation.

## Capacity-relaunch continuation

Recovered receipts, including host-only IDs 41815–41827. IDs 41813 and 41828
were preflight-only and are retired without a Lean charge; no ID is reused.
The prior local tally understated attempts until those receipts were collected.

Checked 41850/41851: the same-public admitted path family has differing pole
sets, and hence a challenge chi for which the two `NoPole` propositions are
opposites. This does not yet prove that the public P_R1 gate accepts that
challenge, that the native oracle realizes it, or that the emitted full body
has the respective success/rejection outcomes. Those are still required for
the D215 counterexample. No availability premise is removed.

Memory failures 41830/41832/41834/41843 were isolated to cardinality conversion:
normalizing a concrete finite function-space enumeration hit the existing
-M7000 limit (peak about 7 GiB, swap 0). Caps were not raised. Replacement:
`PV_OptB_FieldCard.cardDigest_generic` and `PV_OptB_NatCard` prove the shape
abstractly and transport through `Nat.card`; 41850 then checks in 1.98 s at
4,099,516 KiB, swap 0, standard axioms. Failed outputs remain evidence and
are not accepted axioms audits.

The actual emitted retry and entropy steps also check (41837, 41839, 41853,
41854): Rejected recurses; a callback error stops at the entered position;
a non-Rejected body error exits before the next callback. Body outcomes are
explicit hypotheses, not facts asserted about admitted witnesses.
