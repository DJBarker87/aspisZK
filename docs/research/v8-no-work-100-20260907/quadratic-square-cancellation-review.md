# Polynomial square cancellation at a guarded specialization

Working research parent: `9bc0ceee408f432c879ff2239e3ec565dedcd409`.
Executed cached scope/runner parent remains `289d7356c78a4cd493fe61a54f9548f2a0c11298`.

`QuadraticSquareCancellation.lean` proves that, over a field K,

`U^2 = C(a)*H^2*R`, with `a != 0`, `H != 0`, `R != 0`,

implies existence of a **polynomial** V with

`V != 0`, `U = H*V`, and `R = C(a^-1)*V^2`.

The proof first derives `H^2 | U^2`, then uses unique factorization to
derive `H | U`. It does not divide in the fraction field and assume the
quotient is polynomial. The scalar inverse is of the nonzero field value
a, not of a potentially nonunit polynomial. A second checked lemma derives
`natDegree V <= m` from `natDegree R <= 2m` and the nonzero scalar square
representation.

These are the exact cancellation/degree interfaces needed by the checked
Sylvester specialization count. The three nonzero guards are still real
obligations. For a discriminant decomposition they must follow outside
explicitly charged content, H-specialization and leading-coefficient events.
This file neither constructs that global decomposition nor bounds those
events. It changes no proof values or verifier operations.

## Focused verification

Both attempts used the inherited cached NUC scope over Tailscale,
MemoryHigh 8 GiB, MemoryMax 10 GiB, SwapMax 0, Lean `-j1 -M9500`.

| Attempt | Exit | Wall | Peak RSS KiB | Swaps | Result |
| --- | ---: | ---: | ---: | ---: | --- |
| v1 | 1 | 1.05 s | 2,111,452 | 0 | Missing polynomial UFD instance import |
| v2 | 0 | 1.19 s | 2,392,064 | 0 | Added cached GaussLemma import; both audits standard-only |

Command: `bash run_higher_y_nuc.sh <scope> QuadraticSquareCancellation quadratic-square-cancellation-nuc-v2`.
Both exact source snapshots, logs and import manifests are retained.

Source SHA256: `a69a2c842f3697a46f6d0026e582213993f7a8ce8d735027ebf9513144fafe44`.
Olean SHA256: `7f0114384ce4fb4c92baa6611fd1e746446327547ed06485525d95817fb8d833`.
Audits use only `propext`, `Classical.choice`, `Quot.sound`.
