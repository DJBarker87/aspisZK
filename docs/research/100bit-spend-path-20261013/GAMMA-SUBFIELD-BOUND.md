# The two-pad exceptional challenge in the modulo model

`GammaSubfieldBound` proves that the existing nonzero WideExact modulo
sampler returns a value in the QM31 subfield with probability at most

```text
P^4 * 257 / 2^256 ≤ 2^-123,    P = 2^31 - 1.
```

This is an independent uniform 256-bit input-block statement in the
existing `R0C.ModuloField` model. It does not prove the Rust sampler
correspondence or charge adaptive Fiat–Shamir queries automatically.

The proof reuses `gamma_event`, which bounds the mass of a finite bad set
by its cardinality times `257/2^256`. The zero-imaginary-coordinate slice
of the quadratic extension has at most `|QM31| = P^4` elements: its real
coordinate is injective on that slice. The set includes zero, so this is
a conservative bound even though the sampler's output is nonzero.

The final theorem is about the actual model predicate `gamma.im = 0`, not
an arbitrary supplied exceptional set. The numerical inequality is proved
by exact rational arithmetic. This supplies one exceptional-event bound
needed by the [two-pad correction](DUAL-PAD-WORD-BRIDGE.md); universal mask
preimages, the full disclosed-payload law, and efficient simulation remain
separate obligations.

## Proof-engineering evidence

The first attempts exposed elaborator reduction of the enormous concrete
field enumeration while matching a finite-set membership expression.
Increasing recursion depth did not fix it. The final proof uses a generic
coordinate-injection cardinality lemma and makes the concrete bad set
locally irreducible after proving its membership characterization. Later
proofs use that symbolic characterization instead of unfolding the set.

Attempt `gamma-subfield-bound-z` is the final source: exit 0, 1.13 seconds,
2,468,332 KiB peak RSS, zero swap, under 4G/6G/zero-swap limits. All five
axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`.
Failed attempts and the earlier successful cardinality/density source `x`
are retained in `evidence/lean-lift-subfield-20261014/`. The final source
SHA-256 is `2dd2b78cfd584050c37aced3298ffc18cce3377ae2f428055578ea5fdcc31c0e`.
