# R562 — channel target boundary

## Verified field-model result

[`R562ChannelTargetBoundary.lean`](lean/AspisV8R19/R562ChannelTargetBoundary.lean)
compiled in focused run `1791075818702541000` (exit 0; 0.96 s; peak
Lean-child RSS 2,303,768 KiB; swap 0). Its canonical SHA-256 is
`700ab9ae95404bbc255bf1ef25ec6e7bc83abf0ee1232de2c6dc47d5817df468`.

`structured_claim_zero` applies the complete existing
`original_weights_transported_pairing` result to the selected structured
form. Its hypotheses explicitly cover the retained mask, point-1 and point-2
functionals, inactive balance, and both image tails; the source expression
keeps the literal tau updates. `structured_sparse_claim_zero` then uses
`TwoSwapSourceG.original (maskWeights271 half z)`, the exact selected
`TwoSwapSourceTable.order`, and R561's sparse pairing theorem. It does not
invoke the older dense source-mixing model and does not add beta or challenge
premises.

The full saved sources, four attempts, receipts, raw logs, direct-import pins,
checksums, metrics, and complete axiom reports are in
[evidence/r562-channel-target-boundary](evidence/r562-channel-target-boundary).
The final direct imports are `SourceOriginalWeights` SHA
`692851a0e3b153cf363464975553bbe19e98031d6853dab07c354c59dcfa1c18`
and R561 SHA
`2fa3fc771ac16e2512ac0bea523beae3b2d5b1afb0d892bf66a41c02f80d386c`.

## Boundary

R562 establishes only the stated field-model implications. Native Rust writes
and arithmetic, source-execution correspondence, bindings from selected source
conditions to the theorem hypotheses, and universal joint image existence
remain unproved. It does not establish privacy, soundness, or end-to-end
security.
