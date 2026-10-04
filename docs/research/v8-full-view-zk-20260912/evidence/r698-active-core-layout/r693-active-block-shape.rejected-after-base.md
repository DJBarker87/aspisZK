# R693 TwoSwap active block shape (read-only)

Input sources:

- `docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/TwoSwapSourceTable.lean`, SHA-256 `88bedf159e0cf288d514f59c734e8af6f6c42252c9875e02d67d330a0eaa87e7`.
- `docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/T163SourceTable.lean`, SHA-256 `6aaf8bc2e1fce9a5a0116eac8eda44b5ca2032e5dcb5d2824587e05bf8ff3795`.

For each source-code index `j : 0..1023`, this inventory evaluates the
literal table predicate

```
active(j) := !T163SourceTable.isInactive(TwoSwapSourceTable.order(j))
order(j) = swap(127,1023)(swap(126,1021)(j%2 + 16*((j/2)%64) + 2*(7-j/128)))
```

The full increasing ordered list and every nonempty four-slot block are in
[`r693-active-block-shape.json`](r693-active-block-shape.json). The
comma-separated increasing list has SHA-256
`dc9583be4f5c8f52c8b44cd86dcc0a2a951630ac37d5956a0304471ba0d77336`.

## Counts

- Active source-code indices: **214**.
- Minimum / maximum: **114 / 1022**.
- Slots by `j % 4`: slot 0: **66**; slot 1: **39**; slot 2: **68**; slot 3: **41**.
- Nonempty four-slot source blocks: **115**.
- Block occupancy: 17 blocks have one active slot; 97 have two; one has three;
  **none has all four**. Maximum occupancy is therefore three.
- The sole three-slot block is block 159, with slots `[0,2,3]`.

For the proposed high range `j = 4*d+s`, `22 ≤ d ≤ 254`, `0 ≤ s < 4`
(the 233 degree positions whose three nonconstant channels account for the
699-channel count), 212 active indices are in range. The high-range block
occupancy is 17 single-slot, 96 two-slot, one three-slot, and zero four-slot
blocks. The only active source-code indices outside that range are
`[1021,1022]`, which occupy block 255 slots `[1,2]`.

This is a literal integer-table shape analysis. It does not prove an active
minor, a rank statement, a source-to-field correspondence, or any challenge
premise. In particular, the absence of a four-slot block does not itself
settle the proposed scalar-chord/alpha-one minor route.
