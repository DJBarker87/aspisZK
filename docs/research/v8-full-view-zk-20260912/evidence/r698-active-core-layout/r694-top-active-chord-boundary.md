# R694 top active chord boundary (read-only)

This note records the exact source-shaped chord model at output codes 1021 and
1022. It does not assert a rank, a nonzero value, a source-to-field bridge, or
a privacy result.

## Pinned files

- `lean/AspisV8R17/SourceScatter.lean`, SHA-256
  `d6f52f0f8c34364f1c81b63c69832811e29709081607936a5d3528e702a4d7d4`.
- `lean/AspisV8R17/WeightedScatter.lean`, SHA-256
  `5a33cf1c7f5fa122bf3f2bc94ac6c2d4f51a25446f565faf8e3d6e20da413e0c`.
- `lean/AspisV8R19/TwoSwapSourceTable.lean`, SHA-256
  `88bedf159e0cf288d514f59c734e8af6f6c42252c9875e02d67d330a0eaa87e7`.

`WeightedScatter.sourceChord` fixes `n = 512` and the two literal schedules at
lines 25–26. `sourceEdges_bounds` (lines 15–23) supplies only output bounds:
for `sourceEdges half n`, a target is below `n+1`.

## Exact formulas

`finiteChordCoefficient` selects parity (`SourceScatter.lean:214–225`), and
its equivalence theorem reduces the finite model to the padded 1024 input.
With `Q := zeroExtend 1024 q`, `X := sourceEdges half 512`, and
`XX := sourceEdges half 513`, the definitions at lines 42–49 give:

```
sourceChord half q a b c 1021
 = c*Q 1020 + a*Q 1021 + b*scatterValue X (fun i => Q (2*i+1)) 510

sourceChord half q a b c 1022
 = a*Q 1022 + b*scatterValue X (fun i => Q (2*i)) 511
   + c*(Q 1023 - scatterValue XX
          (scatterValue X (fun i => Q (2*i+1))) 511)
```

These are direct substitutions of `1021 / 2 = 510` (odd) and
`1022 / 2 = 511` (even). The finite definitions at lines 169–183 state the
same equations before `finiteChord*_eq` removes the intermediate padding.

Consequently, an assumption only that the four direct top entries
`Q 1020`, `Q 1021`, `Q 1022`, and `Q 1023` are zero leaves:

```
code 1021 = b * scatterValue X  (fun i => Q (2*i+1)) 510
code 1022 = b * scatterValue X  (fun i => Q (2*i))   511
            - c * scatterValue XX
                (scatterValue X (fun i => Q (2*i+1))) 511
```

The available generic bounds permit those scatter outputs: `X` targets are
below 513 and `XX` targets below 514. They do not prove these particular
outputs vanish from the top-entry condition. Existing unit support lemmas
`sourceChord_even_zero` and `sourceChord_odd_zero` (`WeightedScatter.lean:
280–310`) instead require explicit non-membership in `indexTargets` or its
second scatter. No existing top-tail support lemma found here discharges those
conditions at 510 or 511.

## Corrected active-table connection

`TwoSwapSourceTable.order` is `(swap 127 1023).trans ((swap 126 1021).trans
base)` (line 38). For `Equiv.trans f g`, application is `g (f j)`, hence
`order j = base (swap126_1021 (swap127_1023 j))`. The corrected R693 literal
table has 214 active source indices, 213 in `4*d+s` for `22 ≤ d ≤ 254`, and
only source index 1022 is both active and outside that range. Source index
1021 is outside that range too, but is inactive after the corrected order; it
maps to code 1022. The earlier after-`base` calculation remains preserved as
rejected evidence.

The scalar-chord/alpha-one active-minor idea therefore cannot simply discard
the top boundary. This is a limitation of that proposed proof route, not a
privacy-leak claim.
