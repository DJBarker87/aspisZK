# Tag-73 causal challenge binding

## Decision

The old Tag-73 duplex advanced with `SHA256(state || 0x02)` independently of
the sibling output `SHA256(state || 0x01)`.  An adaptive prover could therefore
learn later transcript states before fixing the gamma or alpha-zero output.
The delayed-fold K1.3 branch cannot be closed by relabelling those queries:
their logical role is not determined at first exposure.

Tag-73 profile revision 2 adds an immediate binding record after the gamma and
alpha-zero samplers:

```text
SHA256(
  state_after_sampler ||
  0x00 ||
  62 ||
  challenge_id ||
  canonical_decoded_qm31_le
)
```

`challenge_id` is zero for gamma and one for alpha-zero. The decoded value is
the canonical 16-byte little-endian QM31 encoding already consumed by the
algebraic verifier. The preceding transcript digest already binds the exact
sampler-block chain and stopping point.
The profile binding revision byte changes from one to two, so old proofs fail
closed rather than crossing the transcript change.

## Scope

- V5 and V6 retain their exact transcript.
- The Tag-73 wire body and proof account do not grow.
- q16, Merkle digest width, work difficulties, algebraic relations and all
  proof-system security parameters are unchanged.
- Exactly two additional transcript SHA-256 calls are introduced.
- The fixed binding payload is 17 bytes and its complete absorb input is 51
  bytes.

## Checked foundation

`V7Tag73RawChallengeBinding.lean` proves the binding codec and complete
absorb input are injective. Its printed axiom union is exactly `propext`,
`Classical.choice`, and `Quot.sound`; it contains no `sorry`, `admit`, project
axiom, or `native_decide`.

The Rust sampler test proves that the bounded sampler returns the unchanged
field value and reaches the exact manually reconstructed binding state. A
focused complete V7 prover-to-verifier fixture also accepted with the new
profile and retained the existing sub-30-KiB proof body.

## Formal integration status

The corrected schedule is now integrated through the exact operational ROM
model.  The accepted execution exposes the literal gamma and alpha-zero
sampler traces, their immediate decoded-value binding records, the intervening
event lists, final256, final work and the shared q16 base.  K1.6's exact
resource arithmetic has been increased by exactly two full SHA-256 calls.

`V7Tag73K13BoundChallengeClosure.lean` proves that equality of the immediate
binding inputs forces equality of the decoded gamma and alpha-zero values,
then discharges the corrected pair-coordinate invariant.  Its release-facing
theorem is:

```text
exact_clean_preQ16_trial_union_probability_le_one_forest_of_bindings
```

That theorem reaches the existing one-forest K1.3 probability bound without a
residual alpha/gamma alignment premise.  Every theorem printed by the module
has axiom set exactly `propext`, `Classical.choice`, and `Quot.sound`; there is
no `sorry`, `admit`, project-specific axiom, or `native_decide`.

## Remaining release integration

Production source/Aeneas and CU evidence must be regenerated for profile
revision 2.  `V7Tag73ExactMeasuredCleanK16Assembly.lean` now consumes the
corrected bound directly and no longer accepts the former alpha/gamma
invariants.  Its remaining K1.3 source seam is one deterministic inclusion:
the production q16 query event must be represented by the corrected pre-q16
chronological trial union.  The K1.4 and K1.5 operational bounds must then be
installed before the conditional K1.6 capstone becomes the full end-to-end
theorem.  No release or deployment may reuse revision-1 artifacts.

The same assembly now obtains the K1.4 width-29 bound through
`V7Tag73K14BoundGammaClosure.lean`.  That module fixes the abstract
variable-prefix factorization to the deployed pre-answer gamma controller;
the capstone no longer accepts a bare K1.4 probability inequality.  Its
remaining K1.4 seam is deterministic source data: the pre-gamma extracted
word, the scheduler-native response family, and inclusion of the literal
failure in the corresponding width-29 target.  The only external mathematical
input at this step is the explicitly typed published circle-code theorem.
