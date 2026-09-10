# Characteristic-aware parity-resultant nonvanishing

Working parent: `9bc0ceee408f432c879ff2239e3ec565dedcd409`.
Executed cached scope parent: `289d7356c78a4cd493fe61a54f9548f2a0c11298`.

Two new focused leaves close the field-level nonzero-resultant implication.

`QuadraticParitySeparable` proves that a nonzero squarefree polynomial is
separable if every irreducible divisor has nonzero derivative. A common
prime divisor of R and R' would divide either the prime factor's own
derivative or its complementary factor. The first contradicts separability
of that irreducible factor; the second contradicts squarefreeness. This
works over arbitrary fields, not just perfect fields.

`QuadraticParityCharacteristic` discharges the derivative condition from
`0 < natDegree R < p` over a field with characteristic p. Every irreducible
divisor has positive degree below p, so its leading exponent is nonzero in
the field. The proof reuses V7's symbolic leading-exponent derivative lemma.
It also proves the exact derivative degree `natDegree R - 1`, including the
natural-cast conversion, and concludes nonvanishing of the actual fixed-size
resultant with sizes `(natDegree R, natDegree R - 1)`.

This is suitable for K(Z) without asserting that K(Z) is perfect. It still
requires the literal parity polynomial to map to a **squarefree** polynomial
over K(Z), and the selected degree bound to satisfy the characteristic
inequality. Localization, degree/source transport and the subsequent
fixed-factor event composition remain separate obligations. No numerical
global security term is claimed here.

## Focused evidence

All runs used Tailscale, the inherited pinned cache, and one V8 scope at a
time: MemoryHigh 8 GiB, MemoryMax 10 GiB, MemorySwapMax 0, Lean `-j1 -M9500`.

| Target/attempt | Exit | Wall | Peak RSS KiB | Swaps | Outcome |
| --- | ---: | ---: | ---: | ---: | --- |
| Separable v1 | 1 | 4.44 s | 2,408,632 | 0 | Wrong orientation of the additive divisibility lemma |
| Separable v2 | 0 | 1.09 s | 2,409,772 | 0 | Two standard-only audits |
| Characteristic v1 | 1 | 2.79 s | 6,791,568 | 0 | Natural-cast predecessor conversion missing |
| Characteristic v2 | 0 | 3.00 s | 6,825,656 | 0 | Three standard-only audits |

Exact runner command for each target is recorded in its attempt log;
snapshots and import manifests are retained for all four runs.

Separable source: `fd3001c86a08fc2d31571cedac0596ded10530111c2bdafb11a3d8488950dee1`.
Separable olean: `6b1dd05c93b2c05c7f2098f9ac59c35383064a6846f16da45b09f1f59718a49d`.
Characteristic source: `1ef096400ffb72021aa6a0f1f2fb69bb662039020fef90a849ca8079dcef0f9f`.
Characteristic olean: `86080f6354b4f34e3a4fbf4c8b0a99ed9659c321ea4897fec8f9dbc506d63427`.

All successful audits contain only standard axioms. No verifier, proof
body, transcript or production configuration changed.

## Literal-coefficient resultant descent

`QuadraticResultantDescent.fixed_resultant_nonzero` now transports this
result back from K(Z)[X] to the actual K[Z][X] resultant. It derives mapped
degree equality using the injective fraction-field map and uses the literal
resultant-map and derivative-map identities. The premises are positive
X degree below p and localized squarefreeness; no nonzero-resultant premise
is supplied. The separate `PolynomialParityLocalization.bivariate_parity`
construction establishes the localized squarefreeness.

Focused v1: exit 0, 2.97 s, peak RSS 6,822,688 KiB, zero swaps, one
standard-only axiom audit, same runner and caps.
Source: `2193f539675c02c3cfa7040d2c7a6ae024c98819f85362be79412716ce67f21b`.
Olean: `0d89b6f5e6998090c4f1cb117827c0c6899cd2fa380ebe4ac4c1e0d8cfaff3aa`.
The exact attempted source, log and manifest are retained.
