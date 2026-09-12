# Causal relation-message serialization prerequisite

Scope: functional, field-level producer only. Neither the complete source
verifier nor `SuccessfulAt` is constructed by this leaf.

`SameBodyRelation.lean` defines the actual compact-message shape (six sent
coefficients), omitted-c4 reconstruction, response0-before-alpha0,
final256-before-queries/rho, and three later adaptive responses before their
respective challenges. A continuation is a typed nested strategy, not a
callback returning an already completed body. `produce` executes that strategy
along realised challenges and serializes its responses/final to selected
indices 417–440 and 441–696; it preserves earlier fields 0–416.

`produced_consumes` proves that serializing any such legal strategy yields a
field word that passes every relation-message trace-consistency check. The
correspondence is therefore constructed for produced words, not supplied as a
coherence certificate. `consume_constructs_correspondence` recovers those
equalities from the executable checker. `tail_prefix_noninterference` proves
that equal revealed challenge prefixes imply identical already-sent prefixes.

IMPORTANT: `consume` is a **model trace-consistency checker**, not a newly
installed Rust acceptance check. Its message-equality checks must not be
silently added to protocol acceptance or mistaken for checks done on-chain.
The task of constructing the typed strategy and its realised word from the
actual legal adversary/source/RO execution remains open. This producer solves
serialization consistency inside that model, not the distribution coupling.

## Remaining inputs and boundaries

| Input/interface | Status |
|---|---|
| pre-tau strategy | legal causal shape; actual source/adversary producer open |
| earlier 417 fields | raw supplied prefix; main semantic work separate |
| arithmetic/evaluate7 | explicit operations; QM31 identity and literal-source refinement open |
| ordinary claim | raw earlier value; source ordinary/image preparation open |
| query increment | explicit function of final/schedule/rho; actual authenticated residual link open |
| challenges/schedule | explicit environment; conditional fresh law and FS coupling open |
| roots/nonces/records/frontiers | not represented by this leaf |
| terminal payment/relation acceptance | not asserted |

No predicate assumes ideal acceptance, recovered witness, or candidate
membership. The checker result computes carried claims; it does not prove
their semantic meaning.

## Executed evidence

Local pinned Lean 4.33.1, commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`; first-party import is only this leaf
for fixtures, otherwise `Std` toolchain cache. No Mathlib or historical Aspis
first-party artifacts imported.

Commands in `lean/`:

```
lake env lean -M1800 -o SameBodyRelation.olean SameBodyRelation.lean
LEAN_PATH=. lake env lean -M1800 --run SameBodyRelationFixtures.lean
```

Final local leaf exit 0, wall 2.33s, maximum RSS 712,622,080 bytes, swaps 0.
Fixtures exit 0, wall 0.33s, RSS 664,109,056 bytes, swaps 0. Five fixture checks
pass: adaptive nonvacuity; stale response0/final/late-response mismatches;
intentional nonchecking of a semantic field outside this leaf's scope.
These are model tests, not Rust/SBF/payment executions. `produced_consumes`,
serializer projections and prefix theorem use only standard foundations;
correspondence proof uses `Classical.choice` additionally (standard).
No `sorry` or new axiom retained. A fresh kernel replay is for the parent's
combined root; no independent checker claim here.

Local failed attempts included missing finite-function DecidableEq (replaced
with executable finite pointwise comparison), import search-path omission
(fixed by LEAN_PATH), unsupported Mathlib vector notation (replaced by finite
case functions), and a transparent-index mismatch under rewriting (index
changed to abbreviation; explicit congruence rather than broad congr tactic).
No resource cap was raised; no historical cache rebuilt or modified.

Next producer: actual source/RO interpreter must emit these exact typed stages
from available history and show its serialized field word is the submitted
word. Only then may the relation terminal and authentication bridge consume
this construction as source evidence.

## Follow-on: same-word ordinary and OOD inputs

`SameBodyOrdinary.lean` now constructs all 87 ordinary point claims, the
inactive claim, both 29-lane component-OOD vectors, their forward-power gamma
batches, the repaired scales `[kappa,kappa²,kappa³]`, and the uncorrected ordinary
scalar from one `Word`. It computes x-versus-y interpolation selection, the
fallible chord-coordinate inverse, affine intercept/slope and all three chord
coefficients. Inverse failure returns `none`; there is no invented fallback
or image-validity premise.

Source reference: `inactive_row_binding.rs:129`–153. The selected structured
implementation has the same expressions in `structured_weights.rs:126`–162,
with Horner/shared-gamma evaluation variants. Equality of those optimized
arithmetic kernels to the forward-power fold is NOT proved here.

This is explicitly the **uncorrected** scalar, before subtracting the two
public-weight/interpolant contributions. The frozen mask tables, concrete
statement-point constructor, two required public weight entries and chord
transpose are not supplied as unchecked opaque values. They are left out and
remain the next deterministic source producer. The current function is not
the full `prepare` or `Program.data` constructor.

`prepared_from_same_word` proves projected/scalar/interpolant output identities;
`prepared_inverse_and_chord` proves branch, fallible inverse result and chord
formula identities. These are source-expression refinements for explicit
arithmetic operations, NOT universal field interpolation correctness from
unchecked arithmetic. Literal QM31 operations, inverse soundness, secure-point
sampling/geometry, transcript order and byte canonicality remain independent
instantiations.

Focused leaf command:
`LEAN_PATH=. lake env lean -M1800 -o SameBodyOrdinary.olean SameBodyOrdinary.lean`
exit0, wall0.41s, RSS697,729,024 bytes, swaps0. Only standard `propext` and
`Quot.sound` axioms reported. Ten F17 executable fixtures in
`SameBodyOrdinaryFixtures.lean` passed with `LEAN_PATH=. lake env lean -M1800
--run SameBodyOrdinaryFixtures.lean`: wall2.07s, RSS664,125,440 bytes, swaps0.
They include x/y coordinate selection, actual circle pairs over F17,
interpolation endpoints, same-point inverse failure, and changes to inactive
and OOD fields. They are model checks, not actual Rust or cryptographic-rate
evidence. No protocol acceptance changes or new proof bytes.
