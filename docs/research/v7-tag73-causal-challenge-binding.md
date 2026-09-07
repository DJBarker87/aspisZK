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
  blocks_used ||
  raw_blocks_padded_to_12
)
```

`challenge_id` is zero for gamma and one for alpha-zero. `blocks_used` is in
`1..12`. Every unused byte in the fixed 384-byte raw-block region is zero.
The profile binding revision byte changes from one to two, so old proofs fail
closed rather than crossing the transcript change.

## Scope

- V5 and V6 retain their exact transcript.
- The Tag-73 wire body and proof account do not grow.
- q16, Merkle digest width, work difficulties, algebraic relations and all
  proof-system security parameters are unchanged.
- Exactly two additional transcript SHA-256 calls are introduced.
- The fixed binding payload is 386 bytes and its complete absorb input is 420
  bytes.

## Checked foundation

`V7Tag73RawChallengeBinding.lean` proves the fixed binding codec and complete
absorb input are injective. Its printed axiom union is exactly `propext`,
`Classical.choice`, and `Quot.sound`; it contains no `sorry`, `admit`, project
axiom, or `native_decide`.

The Rust sampler test proves that the bounded sampler returns the unchanged
field value and reaches the exact manually reconstructed binding state. A
focused complete V7 prover-to-verifier fixture also accepted with the new
profile and retained the existing sub-30-KiB proof body.

## Remaining formal integration

The accepted Tag-73 execution schedule must now represent the two binding
absorbs, connect their padded block inventories to the literal sampler traces,
and use input equality to close gamma/alpha-zero equality in the corrected
K1.3 pair invariant. K1.6's exact oracle-call arithmetic must increase by two.
Production source/Aeneas and CU evidence must be regenerated after that formal
closure; no release or deployment should reuse revision-1 artifacts.
