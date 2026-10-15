# Independent review by `/root/d18_point_weights`

Reviewed the selected-opening pairing theorem and evidence read-only; no build
was run.

`acceptedPairing_iff_coefficientChecks` states an equivalence, for supplied
payloads, words, functionals, and challenges, between the existing
`MatchingSupport.AcceptedPairing` predicate on the constructed data and three
explicit coefficient checks. Those checks are: the second polynomial at
`alpha1` equals the dot product against the two dual folds; coefficients 0
and 4 of the second opening payload sum to one quarter of the first
polynomial at `alpha0`; and coefficients 0 and 4 of the first opening payload
sum to one quarter of the kappa-weighted `parts` sum. The proof unfolds the
model predicates, uses the polynomial boundary/evaluation identities, and
then rewrites the `parts` sum using `SelectedOpeningClaims.parts_weighted_sum`.
The statement has no extra premises beyond the explicit data arguments.

This is an equivalence of model predicates for supplied values. It does not
prove Rust execution, accepted-proof correspondence, source recovery, or that
any of the coefficient checks holds.

Evidence checks passed: the source, final snapshot, and successful attempt
snapshot have SHA-256
`bf227c7e561bd3ef66c537f0769565f365d6abff3aaff93aa71c62b3369c1c7c`; the
receipt records exit 0, 1.99 s, 3,578,448 KiB peak RSS, zero swap, and the
4G/6G/0 cgroup. The log contains one wrapped axiom report, listing only
`propext`, `Classical.choice`, and `Quot.sound`. Both object archive members
match the manifest hashes and sizes, and the pre-review `SHA256SUMS` passed.
The direct `SelectedOpeningData` source/object pins match their bundle; no
source/refinement claim is inferred from that dependency.

No discrepancy was found in the theorem statement or evidence.
