# Higher-Y residual status

Date: 2026-09-10. Branch parent at the start of this note:
`24571219239106fd6c769f60ad7fb49725bef936`.

## Checked fixed-early-C1 endpoint

`SelectedHigherYProbability.higher_probability_bound` is the current
degree-at-least-three endpoint.  Under the literal fixed result
`earlyC1 e.c1 = some p`, checked circle/OOD data, nonzero gamma domain and
the explicit complement of the pre-OOD pair-root obstruction, it proves

    higherProbability
      <= 234126 / |Gamma|
       + integratedBudget(q,Gamma,A)
       + q / |G| + 18 / |A|.

HIGH and LOW are a disjoint partition of the same actual compact suffix.
HIGH uses the `117077/|Gamma|` cardinality/unit bound.  LOW uses the checked
layer cake and its `117049/|Gamma|` common-row root charge.  The rho and later
relation repairs are charged once.  The final remains adaptive in tau and
alpha.  The exact q22 screen with the separately checked ideal pair sampler is
103.84730703698959 bits.  This is not yet the all-acceptance or Fiat--Shamir
theorem.

The previous machine-readable `max(sparse,dense)` shortcut was incorrect:
the sparse helper-Good alternative controls only HIGH.  LOW is present in
both helper branches.  The current checked composition does not use that
shortcut.

## The remaining early-C1-none class

`SelectedHigherYNoEarlySupport.no_early_support_cover` proves that when
`earlyC1 e.c1 = none`, every image-valid quotient outside one fixed set of at
most 63 gammas has at most 252847 matching complete fibres.  It does not erase
the middle interval 200808 through 252847.

Three exact screens reject straightforward completions:

| Attempt | Result | Consequence |
| --- | ---: | --- |
| Extend the present layer cake to 252847 | 97.1879093395618 bits | Fails q22 by 2.812091 bits |
| Retain the present tail form | Needs 7.06537007x less query incidence | No such reduction follows from uniqueness alone |
| Stronger 29-node common-support cover through quotient support 240604 | 98.68503 bits | Still below 100 |

With the present low layer through 200807, one sufficient replacement theorem
would bound the middle-gamma union by 34810510 before applying its capped q22
matching mass.  That number is a falsifiable target, not an established cap.

## What relation structure does and does not yet give

For a fixed gamma, two quotients with at least 200808 matching fibres must be
equal: their supports intersect in at least 139472 fibres, above the concrete
encoder overlap cap 256.  Thus the middle quotient is common across retained
factors and all later kappa/tau/alpha histories.  This removes an adaptive
selection ambiguity but does not reduce the number of gammas: one factor may
still carry the whole `239599331` regular-incidence budget.

The research `Execution` abstraction permits arbitrary row weights.  The real
callback is narrower: before chord transport it uses

    inactive + kappa*eq(z) + kappa^2*eq(successor(z))
      + kappa^3*eq(xor12(z)).

These four nonzero linear observations do not by themselves imply a
componentwise C1 support of 245609 fibres.  Existing V7 semantic-to-witness
bridges consume coherent/shared-support extraction and therefore cannot be
used to manufacture that missing premise.

The V7 fixed-Hensel development cannot presently supply the missing reduction
by truncating to a small Taylor jet.  The selected decoder reads natural
message rows through 1017 and validates all 1024 rows.  Those rows are not low
Taylor coefficients: even the constant natural message maps to the literal
degree-1024 GRS numerator `(1+t^2)^512`.  The existing V7 support-to-discrepancy
bridge also assumes the candidate degree bound it consumes.  At local degree
one and weight 28, order 145 would cost 33827189 incidences and order 146 costs
34061287, while the complete degree-1024 route costs 239599331.  No sound
order-145 truncation follows from the payment layout.

## Why `earlyC1 = none` is not the failure event

There is a direct boundary obstruction to the stronger implication
`acceptance -> earlyC1 != none`.  Begin with a valid trace and, before any
challenge, alter one committed C1 column on exactly 16536 complete fibres.
The original tuple then has 245608 own-support fibres, one below the selected
threshold.  Any different tuple matches on at most `16536 + 256 = 16792`
fibres by the checked encoder-overlap bound.  Hence `earlyC1 = none`, although
the original valid witness still exists and schedules avoiding the altered
fibres occur with exact probability

    choose(245608,22) / choose(262144,22) ~= 0.2384686.

This is a symbolic classifier falsifier, not a payment forgery and not yet an
executed complete-transcript fixture.  It shows that eliminating `none` is
strictly stronger than knowledge extraction.  The global event must remain
`acceptance AND the specified extractor fails`.

## Current extraction direction

The middle-support uniqueness result suggests a causal rewind route rather
than another direct bound on `earlyC1 = none`:

1. At a fixed pre-alpha prefix, four distinct accepted alpha continuations
   whose actual finals have the required support determine the same canonical
   quotient.  The existing cubic-fold interpolation results are the intended
   deterministic core; the acceptance-to-support and fork accounting remain
   explicit premises until proved.
2. Repeating this at 29 distinct gamma values with the same earlier committed
   prefix gives enough evaluations to interpolate the degree-28 component
   curve.
3. The reconstructed component tuple can then feed the checked claim-transport
   and payment-witness bridges.  Mathematical interpolation, executable
   extraction, Fiat--Shamir forks/restorations and running time are separate
   obligations.

This route preserves the adaptive post-alpha final: it is the collection of
accepted forks, not an illicitly early frozen final, that determines the
quotient.  It also adds no verifier messages or proof bytes.  It is not yet a
global raw or Fiat--Shamir extraction theorem.  No grinding credit, byte
increase or optimistic primitive error is used in this status.
