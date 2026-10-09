# Residual recovery closure for the selected ideal game

Status: **kernel-checked conditional closure**, not global V8 soundness.

This continuation closes the previously open high/far residual-recovery
branch for the selected ideal execution model. It does so without assuming
candidate membership, exact polynomiality of the received oracle, a target
fixed before its actual selection time, or a successful recovery provider.
The final polynomial remains adaptive after the earlier challenges.

## Checked chain

| Layer | Checked result | Deliberately not claimed |
| --- | --- | --- |
| Middle image recovery | One fixed pre-OOD family of size at most one; every qualifying image-valid candidate is either in the same fixed pair-root event, in one fixed gamma set of size at most 104, or is the same-Q recovered family member on its own support | Actual Rust prefix construction, authentication, or efficient extraction |
| High residual | An actual high witness outside the fixed pair-root and gamma exceptions is `RecoveredHigh` for that same Q and family | `earlyC1 = some` or a payment witness |
| High/LOW partition | Higher-and-unrecovered is exactly the disjoint sum of high-and-unrecovered and actual LOW, with the same suffix | Equality to all verifier acceptance |
| Conditional composition | Outside the literal product pair event, the residual mass is at most `117153/|Gamma| + integratedBudget + q/|G| + 18/|A|` | Fresh random-oracle challenges or source refinement |
| Outer pair adapter | The two pre-OOD obstruction polynomials are combined before either OOD point; the complete two-root event has degree bound 90,407,376 and preserves abort/history dependence | A deployed transcript theorem |

The final adapter is
[`SelectedResidualRecoveryBound.lean`](experiments/SelectedResidualRecoveryBound.lean).
Its prerequisites are
[`SelectedResidualHighRecovery.lean`](experiments/SelectedResidualHighRecovery.lean),
[`ResidualRecoveryCompositionV8.lean`](experiments/ResidualRecoveryCompositionV8.lean),
and
[`SelectedMiddleImageRecovery.lean`](experiments/SelectedMiddleImageRecovery.lean).
Each focused report records exact source snapshots, commands, exit status,
wall time, peak RSS, swap, provenance, and `#print axioms` output. All retained
green declarations use only `propext`, `Classical.choice`, and `Quot.sound`;
none uses `sorryAx` or a new axiom.

## Exact selected arithmetic

For `q = 22`, `|Gamma| = |QM31|-1`, and the selected alpha/relation domains,
the checked symbolic expression is instantiated by
[`residual_recovery_probability.py`](experiments/residual_recovery_probability.py).
The exact rational result is recorded in
[`residual-recovery-probability.json`](residual-recovery-probability.json).

| Term | Approximate mass |
| --- | ---: |
| Product pair, degree 90,407,376 | `1.807044305915173609e-59` |
| Fixed middle gamma set, `104/|Gamma|` | `4.890056508529156062e-36` |
| LOW common roots, `117049/|Gamma|` | `5.503617541027203730e-33` |
| LOW integrated query/alpha budget | `4.379777686740350791e-32` |
| One shifted-query/later-repair suffix | `1.880790964818906178e-36` |
| **Conditional total** | **`4.930816525590405970e-32`** |

The total is approximately **103.9998724649 bits** and is strictly larger
than `2^-104`. It consumes about **6.25055%** of a `2^-100` budget. Adding
the separately proved optional component-claim root charge `28/|Gamma|`
gives approximately **103.9998339447 bits**, or **6.25072%** of that budget.
Neither number includes grinding credit.

## What remains for global soundness

The residual-recovery branch is closed only after the fixed-prefix and
ideal-law hypotheses in the theorem signatures are supplied. Global V8
soundness still requires all of the following:

1. A deterministic source refinement from actual parsed, authenticated
   commitments and the repaired verifier callbacks to the theorem's
   `Execution`, `CandidateClassifies`, checked OOD data, and terminal event.
2. A proof that actual acceptance supplies the ordinary-row condition used to
   transport all 87 component claims, charging the same relation-repair events
   exactly once.
3. A resource-bounded extractor from authenticated C1 access to canonical
   coefficients and then to a witness satisfying the real payment, ownership,
   path, nullifier, context, and atomic-settlement validator.
4. A resource-bounded Fiat--Shamir theorem covering oracle prequeries,
   repeated transcripts, forks/restorations, retries, and runtime. The ideal
   challenge laws are not a claim against unlimited offline search.
5. A full-view zero-knowledge argument for the repaired image/row transcript.

Authentication failure, replay/fuel aborts, missing responses, cached/advance
challenge mismatch, and source-coordinate/terminal-unit mismatches remain
visible obligations. They have not been assigned optimistic numerical
probabilities.

## Wire and performance scope

The proof-body model is unchanged:

```text
697*16 + 52 + 24 + 22*621 + 2*296*26 = 40,282 bytes
```

No proof values, nonces, queries, or rounds were added by this mathematical
closure. The work contains no new complete-transaction CU measurement and
does not establish parity with selected V7. The earlier structured verifier
optimisations and their measurements remain a separate engineering gate.

## Decision

QM31 q22 remains the primary V8 direction. The principal arbitrary-oracle
high/far recovery gap now has a non-circular conditional bound with about four
bits of local margin over 100. The decisive next experiment is the actual
acceptance-to-ideal-event refinement for one complete transfer path, coupled
to authenticated C1 extraction and the checked payment validator. Failure
there would identify a concrete source or extractor gap; success would let the
remaining probability ledger compose against the real verifier rather than
another abstract classifier.
