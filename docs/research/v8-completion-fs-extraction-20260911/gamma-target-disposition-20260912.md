# Gamma target disposition — 2026-09-12

`lean/FSV8GammaTargetDisposition.lean` adds the correct restoration-side
dichotomy for the computed gamma candidate input. In the V7 origin state it
is classified as either:

1. an input already represented in adversary `q1`;
2. a prior table target (`lookupEntry` returns an entry), retained as the
   prior-target/hazard branch; or
3. absent from the table, which is the exact lookup precondition for a V7
   programming attempt.

`gamma_target_disposition` specializes this to
`List.ofFn afterNonce.digest ++ [1]`. No verifier event is misclassified as
adversary q1, and neither nonmembership, freshness, programming success,
fork success, resource room, acceptance, ROM coupling, nor probability is
assumed. The existing K1.6 programming/fork modules can consume branch (3)
once their concrete origin and resource adapters are supplied.

Evidence: `results/gamma-target-disposition-v1/report.json`.
