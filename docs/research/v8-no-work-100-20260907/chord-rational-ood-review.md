# Polynomial reconstruction to batched OOD correctness

The new [ChordRationalOOD.lean](experiments/ChordRationalOOD.lean) closes a
deterministic interface: a reconstructed polynomial chord quotient forces the
two gamma-batched OOD answers to equal the actual circle evaluations of the
same original-code message. It does **not** assume image validity, a degree
bound on the reconstructed quotient, or nonzero chord values at the OOD
points. Those points are chord zeros, so a division-based proof there would
be inappropriate.

## Exact statement and source convention

For `U : Fin 1024 → K`, the new definition constructs the four radial lanes
from the actual natural coefficient lanes:

```
radialLanes U j =
  naturalCoefficientPolynomial (coefficientLane 256 j U)
    composed with (2 X - 1).
```

The source first-fold domain coordinate is `T2(x)=2x²-1`; the cleared
four-component algebra instead uses `s=x²` and `t=1-s`. The explicit
composition accounts for that difference. The proven `radial_lanes_value`
identifies the four entries in `[1,y,x,xy]` order with the existing literal
`ComponentOODBinding.circleFunctional`, using the V7-consumed
`initialP0_eval_lanes` and `initialP1_eval_lanes` identities.

The main theorem `reconstructed_batched_ood` has these inputs:

- the actual `OODInterpolant.Data` and its checked interpolation inverse;
- both defining OOD points satisfy the circle equation;
- a message `U` and polynomial-vector `q` satisfying
  `radialLanes (U - d.interpolant) = product X (1-X) q (line (C a) (C b) (C c))`.

Its conclusion is exactly

```
circleFunctional d.x0 d.y0 U = d.batch 0
circleFunctional d.x1 d.y1 U = d.batch 1.
```

The proof evaluates the polynomial-vector product, invokes the already proved
`product_value`, and uses `Data.chord_at_points`. Linearity moves the
interpolant subtraction, and `Data.eval_at_points` identifies its values with
the two submitted gamma batches. Equal-x OOD pairs retain the existing legal
y-interpolation branch. No selected image theorem is used in this proof.

## Relation to the four-divisibility result

[ChordRationalDivisibility.lean](experiments/ChordRationalDivisibility.lean)
constructs `q` from four exact cleared discrepancies at distinct alpha values,
under a nonzero *polynomial* chord-norm premise. Its product conclusion has
the same orientation as this leaf, after unfolding `radialS=X` and
`radialT=1-X`. This report does not call the two separate declarations a
completed actual-verifier theorem: the composed source input must use exactly
`radialLanes (U-I)`, and still needs actual fixed raw received data equal to the
encoding of `U`. A polynomial representation of arbitrary helper oracles is
not supplied here.

The four finals may differ and may be chosen after their alpha challenges.
Across the four mathematical evaluations the raw message, chord and OOD
answer prefix must remain fixed. The construction is not an executable
rewinding extractor or a source/Fiat–Shamir coupling theorem.

## Scope safeguards and remaining interface

The conclusion is **batched**, not individual, OOD correctness. A wrong
component answer can cancel at a particular gamma. The existing
`ComponentOODBinding.ood_error_nonzero`, `ood_error_degree` and
`ClaimTransport.component_error_eval` are the appropriate next ingredients
for a fixed-before-gamma tuple and a genuinely fresh gamma. The full
component error retains degree at most 28.

The exact selected quotient/image endpoint is separate and not implemented
in this leaf. One non-circular plan is:

1. Construct quotient radial lanes of degree at most 255 from the four
   degree-255 finals; the current divisibility theorem alone does not expose
   that cap.
2. Convert radial coordinates back to final coordinates, use
   `NaturalProjectionCore.coefficients_polynomial`, and interleave the four
   actual coefficient lanes.
3. Derive the full polynomial-pair identities for chord multiplication.
   Existing `V5GoodGateSparseShift.naturalLinePoly_even/odd` and
   `naturalCoefficientPolynomial_eq_basisSum` support an exact polynomial
   lane bridge, without inferring polynomial equality merely from a small
   finite set of evaluations.
4. The resulting full even/odd products equal `initialP0/1(U-I)` and therefore
   have degree at most 511. `NaturalChordImage.selected_image_iff` then
   **derives** `Q1023=0` and `b*Q1022-c*Q1021=0`. The existing natural
   projection and polynomial-pair injectivity lemmas can finally identify
   `d.original Q=U`.

`SelectedQuotientOriginal.encoded_original`, `fibreBad_card` and
`ComponentOODBinding.original_point_values` require the image equations;
they cannot be used to establish those same equations circularly.

There is also a pole distinction. Polynomial divisibility gives a global
polynomial rational quotient, but not necessarily the same values as the
**totalized** received-word division at chord zeros. Four cleared identities
therefore must not be passed directly to a theorem demanding four globally
exact folds of that totalized word. The existing
`PartialFoldSelected.four_selected_support_folds_recover` can use a common
nonpole support if that alternative route is needed. The Rust reference
`relation_callback.rs::opened_values_reference` rejects a queried zero
denominator; the Lean totalization is an analytical overapproximation, not a
source claim that zero denominators are accepted.

## Evidence and reproduction

Command, run once:

```
bash docs/research/v8-no-work-100-20260907/experiments/run_chord_rational_ood.sh \
  docs/research/v8-no-work-100-20260907/experiments/chord-rational-ood-v1.log
```

[Evidence](experiments/chord-rational-ood-v1.log): exit 0; Lean 4.32.0;
20.13 seconds wall time; peak RSS 5,587,599,360 bytes; zero swaps. The six axiom
audits contain only `propext`, `Classical.choice`, and `Quot.sound`. The
serialized runner uses `-M7000` and the existing aggregate 7-GiB guard, with
no package replay or dependency rebuild.

Research source pin: `edb199c12fcc41f00330298b95b4736f60ac6f3a`.
The borrowed V7-consumed formal closure is checked against immutable main
pin `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`; the log records the source and
olean hashes transitively before and after checking. New chord algebra is
independently pinned to its green source/olean hashes. Concurrent main was
`174c63cd6df94b8253c7960b92a36a8bc0fccc77` at the run and was not modified.

- New source SHA256: `f266904c89057a7afe89ad5a43b79136e4ca5e210ec891e6486aee4ef0c0abb1`.
- New olean SHA256: `0ef5aeb2fbf0622085583afb71d684db331151cd78f4faf66ffa3f37d499397b`.
- Runner SHA256: `8ef1917fca06f9bfd802657aba81278bab4e947b47c135c848ee9512bdd9fd42`.

This is a proof-only research interface. No proof-body fields, verifier
operations or runtime source changed; the model remains 40,282 bytes. No new
security subtotal, source refinement, full-view hiding result, replay
extractor or complete-transaction CU claim follows from this leaf alone.
