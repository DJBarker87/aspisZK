# R693 TwoSwap active block shape (read-only, corrected composition)

Input sources:

- `docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/T163SourceTable.lean`, SHA-256 `6aaf8bc2e1fce9a5a0116eac8eda44b5ca2032e5dcb5d2824587e05bf8ff3795`.
- `docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/TwoSwapSourceTable.lean`, SHA-256 `88bedf159e0cf288d514f59c734e8af6f6c42252c9875e02d67d330a0eaa87e7`.

For each source-code index `j : 0..1023`, this inventory evaluates:

```
active(j) := !T163SourceTable.isInactive(TwoSwapSourceTable.order(j))
order(j) = baseNat(swap(126,1021)(swap(127,1023)(j)))
baseNat(j) = j%2 + 16*((j/2)%64) + 2*(7-j/128)
```

`Equiv.trans` applies the right-hand equivalence first, so this is the literal
Lean order definition. The earlier after-`baseNat` calculation is retained as
`r693-active-block-shape.rejected-after-base.*`; it is not used below.

## Checks

- `order(1023) = 1023`, matching `TwoSwapSourceTable.pivot_fixed`.
- `order(1021) = 1022` and `order(1022) = 1008`.
- For every `j < 89`, the computed value equals
  `16*(j/2)+14+j%2`, matching `TwoSwapSourceTable.first_pad_images`:
  `True`.

## Counts

- Active source-code indices: **214**.
- Minimum / maximum: **114 / 1022**.
- Slots by `j % 4`: slot 0: **66**, slot 1: **38**, slot 2: **69**, slot 3: **41**.
- Nonempty four-slot source blocks: **115**.
- Block occupancy: 17 blocks have 1, 97 blocks have 2, 1 blocks have 3; **none has all four**.
- The full increasing list and every nonempty block are in
  `r693-active-block-shape.json`; its comma-separated list SHA-256 is
  `1a22e86f878e7b371bf84afc3f2003d0a9e6aa3093119f6682cb3d0223e39fbf`.

For the high range `j = 4*d+s`, `22 ≤ d ≤ 254`, `0 ≤ s < 4`, there are
**213** active indices. The sole active source-code index outside it is
`[1022]`. The high range has 16 blocks of occupancy 1, 97 blocks of occupancy 2, 1 blocks of occupancy 3 and no full block.

This is literal integer-table shape analysis only. It proves neither a rank
statement nor a source-to-field correspondence. The scalar-chord/alpha-one
minor route is limited by this shape: its proposed high-699 witness has at
most **213** of the 214 active rows. This is a failed proof route, not
a privacy-leak claim.
