# Literal check bridges checkpoint — 2026-10-15

Three additional model bridges passed focused Lean compilation and independent
root artifact review. They are inputs to the conditional terminal composition;
they do not establish that the deployed verifier satisfies the model premises.

| Target | Checked result | Reused work |
| --- | --- | --- |
| `LiteralSemanticPolynomialChecks` | Reverse Horner equals evaluation of the decoded 28-coefficient polynomial; the boundary accumulator equals `p(0) + p(1)` | `SemanticCoefficientCodec`, `OpeningPolynomialView`, and the induction route of the historical `AspisV8R17.sourceMixHorner_eq_sum` |
| `LiteralPairingChecks` | Given a successful matching-data read, `AcceptedPairing` is equivalent to the explicit reader and coefficient checks | `LiteralMatchingFacts`, `SelectedOpeningPairing` |
| `LiteralQueryRhoTranscriptSupport` | Full-list matching-data reads agree with the query-prefix view; the explicit query/rho checks and no-hit imply matching support at least 9558 | `LiteralQueryRhoSupport`, `LiteralReadStability`, `GenericNoHitIndex` |

The query/rho support result **assumes** the successful row-31/32 entry forms,
their validity, decoded query map, first-match facts, and zero residual batch
equation. It does not derive these facts from verifier acceptance.

## Focused verification

All targets exited 0. Reported memory is sampled aggregate process-group RSS;
swaps are the process swap counts from `/usr/bin/time -l`, not host swap usage.

| Target / attempt | Source base | Wall seconds | Peak RSS KiB | Process swaps | Exported axiom reports |
| --- | --- | ---: | ---: | ---: | ---: |
| `LiteralSemanticPolynomialChecks` / `semantic-polynomial-checks-b` | `709a60244` | 57.290 | 4,884,896 | 0 | 2 |
| `LiteralPairingChecks` / `pairing-checks-b` | `2ee03b0c5` | 102.130 | 3,870,656 | 0 | 1 |
| `LiteralQueryRhoTranscriptSupport` / `query-rho-transcript-support-b` | `2ee03b0c5` | 75.013 | 4,534,528 | 0 | 2 |

The reported declarations use only standard Lean axioms (`propext`,
`Classical.choice`, `Quot.sound`); the successful logs have no `sorryAx` or
kernel errors. Exact source/object hashes, commands, failed predecessors and
receipts are retained in the corresponding `evidence/lean-literal-*-20261015`
bundles. The root independently reviewed manifests, source pins, archived
objects, receipts, process swaps and final axiom logs:

- [Polynomial artifact review](../evidence/j1-literal-semantic-polynomial-checks-review-20261015.json)
- [Pairing artifact review](../evidence/j1-literal-pairing-checks-review-20261015.json)
- [Query/rho artifact review](../evidence/j1-literal-query-rho-transcript-support-review-20261015.json)

## Scope and next dependency

The previously committed `LiteralTerminalSpend` theorem produces a witness
accepted by the spend checker under explicit model conditions and no-hit.
`LiteralTerminalRunSpend` is being checked to derive its Good, pairing and
cardinality premises for an actual protocol transcript from the lower-level
checks. Its failed attempts are not counted as proof results here.

Source acceptance to these checks, commitment/Pool correspondence, concrete
sampler and query-budget correspondence, efficient extraction, the full
probability composition, privacy, and current runtime certification remain
separate obligations. This checkpoint does not certify the requested 100-bit
private spend in at most two verification/settlement transactions.
