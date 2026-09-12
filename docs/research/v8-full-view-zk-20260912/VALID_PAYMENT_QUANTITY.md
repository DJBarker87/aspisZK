# Fixed-schedule certificate on valid payments

This note records the semantic meaning established for the supplied q22
schedule `0..21`. Arithmetic is in M31, with modulus `2^31 - 1`.

## Exact opened-value functional

Only six of the certificate's 88 coefficients are nonzero:

```text
L(T) = 1508290849 E(T)[16]
     + 1480589898 E(T)[17]
     +  639192798 E(T)[18]
     +  666893749 E(T)[19]
     -             E(T)[24]
     +             E(T)[26].
```

Using the actual `CircleEncoder`, this is a 384-row functional on column 3.
Its support is every row `16*b+d`, for `0 <= b < 64` and
`d in {1,2,5,6,9,10}`. In particular, the coefficient of row 1014 is
`170822063`, which is nonzero.

The supported semantic cells include Poseidon intermediate states, forest-path
cells, value bits, and commitment limbs. The tail coefficients are:

| Row | Weight | Valid-transfer meaning in column 3 |
|---:|---:|---|
| 1009 | 1610780855 | input-value bit 13 |
| 1010 | 705742178 | recipient-value bit 3 |
| 1013 | 1457471266 | change-value bit 13 |
| 1014 | 170822063 | zero before repair; overwritten by inverse product |
| 1017 | 799606937 | second input-pair commitment limb 1 |
| 1018 | 1547437776 | change-commitment limb 1 |

## Repaired valid-transfer value

The generated positive adapter runs after ordinary masking. Rows 1014 and
1015 in column 1 are relation-used, unmasked cells holding the recipient and
change values. It rejects zero and writes

```text
column3[1014] = inverse(recipient_value * change_value).
```

The supplied certificate annihilates every surviving reconstructed column-3
mask direction. Consequently, on a valid repaired transfer,

```text
L(final column 3)
  = L(semantic column 3)
  + 170822063 * inverse(recipient_value * change_value).
```

The focused Rust test confirmed this identity for seven positive splits of an
input value 1000 and three mask seeds per split. The pre-overwrite functional
changed with the seed; the final functional did not. Numeric outputs are in
`evidence/valid-positive-transfer-values.json` and the retained test body is
`rust/valid_positive_transfer_quantity_test.rs`.

## Privacy interpretation

This advances the finding beyond an arbitrary trace-cell counterexample: the
opened values determine a real, mask-seed-invariant function of every tested
valid payment trace. The function contains an explicit inverse product of the
two private output values and many other witness-derived trace cells.

It is not yet a demonstrated privacy break. Changing the amount split requires
recomputing the public recipient and change commitments and the candidate
afterstate, so the experiment does not provide two valid witnesses for one
public statement. Nor has it proved that a witness-free efficient simulator
cannot derive or sample this whole functional from that public view. Joint
conditioning on earlier proof disclosures also remains undone.

The correct status is therefore a concrete valid-trace simulator obstruction
for one schedule, not a same-public distinguisher and not a global ZK failure.
