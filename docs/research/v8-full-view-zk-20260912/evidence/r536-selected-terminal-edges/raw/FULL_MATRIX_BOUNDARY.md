# R117 terminal composed diagnostic — focused boundary

`run5.log` records one changed, isolated release diagnostic. It evaluates 630
labelled combinations: three `z` inputs, five alpha tuples, three beta values,
two nonzero `(kappa, tau)` modes, and seven final-256 vectors. The final
vectors are units 0, 64, 128, 192, 127, and 255 plus one deterministic random
vector. It uses OOD-derived `abc`, actual `coin_weights_into(z, coins)`, the
actual owned-primal source fold, and a nonzero rho per challenge case.

It checks source original-weights/reference equality, the R106 result against
the legacy scalar reconstruction, R106 plus image against a dense source
quotient dot, the query terminal against dense query coefficients, and their
composed sum. The run passed. This is runtime differential evidence for those
inputs and components only. It does not establish source-wrapper equivalence,
Fiat--Shamir distribution, privacy, soundness, or end-to-end security.

Earlier unlabelled failures remain preserved. Their final-vector attribution
was withdrawn in `CASE_ATTRIBUTION.md`.
