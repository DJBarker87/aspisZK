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
