# Explicit phase transport, stage 1

Owner-authorized continuation of RPz6. The historical e5c186ba3 larger producer
is the one the Tx1 bridge was proved against. Neither producer has been shown
to be a complete extraction of the frozen D188 pin; this provenance remains
OPEN. No extraction/source-to-ELF claim follows from these transports.

RPz7_PhaseIso defines both maps constructor-by-constructor (all 11 constructors,
including U8/Usize payloads), their two round trips and an Equiv. Callback,
optional-observer and arbitrary observer-consumer transports retain effects
and release None. The S1 carrier is explicitly FirstCaller.Phase; we do not
change the producer's verifier.Phase or assert their type equality.

The exact selected S1SemanticPhaseV1 source (683c80e4…) has ZERO theorems. Its
sole declaration is the duplicate Phase abbreviation and its sole audit is
#print axioms on that abbreviation. The replacement removes that declaration;
there are no original theorem names to suffix or proofs to weaken.

| Original export | Replacement | Statement comparison |
|---|---|---|
| verifier.Phase := FirstCaller.Phase | RPz7_PhaseIso.Phase := FirstCaller.Phase | Same expanded retained carrier; different alias name avoids producer collision |
| No original theorems | No restatements required | Empty per-theorem comparison table |

Validation and exact consumer inventory follow in later stage receipts. Only
RPz7-prefixed files in this evidence directory are modified. No shipped source,
session A worktree/candidate, wallet key, runtime trust item or ELF is changed.

Validation: RPz7_001 passes (wall1.681s, peak3855984KiB,swap0);
RPz7_002 passes (wall1.45s,peak3839416KiB,swap0). Exact values and all
source/dependency hashes, argv, revision, limits and printed axioms are in the
receipts. All equivalence/roundtrip declarations use no axioms or Quot.sound.
One admitted 6G/8G/Swap0/Tasks64 scope at a time; Lean-j1-M7000.

RPz7_phase-use-inventory.json lists all legacy carrier use sites selected for
transport, including qualified/open-namespace references. Observer-taking
functions: VerifyPrefix.Finish (type), VerifyPrefix.mark, VerifyPrefix.verify,
FinishModel.finish, S1SemanticCode.Finish (type), S1SemanticCode.finish,
S1SemanticCode.verify. Remaining sites are theorem binders or applications of
these functions (finish/verify bounds, roots, numeric, budget, erasure,
association and Claims consumer). Generic callback/observer/consumer laws cover
all result and effect types; concrete consumer specializations are supplied in
RPz7_PhaseConsumers.lean and require their rebuilt dependencies before checking.
No source mark is changed into an observer callback: its original body is ok().
