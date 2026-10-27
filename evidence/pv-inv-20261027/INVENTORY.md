# Inversion inventory — source baseline 9c4bfcc830c09f8d85fd1ed7996f8d9dcf059c84

Entry: `aspis-r1-cost-probe::prover::prove_masked_retrying[_with]` →
`prove_masked_with_attempt` → `host_semantic::build_with_material` →
`prove_from_semantics`, with `r1p-check`, private leaf salts and Variant S2.
This is the deployed-prover route under review, not the older `aspis-prover::prove`.
Every candidate spelling under crates plus the externally located certificate
producer is captured in candidates.json, with source hashes. This is a lexical
cross-check; the reachable families below are a source call-graph review.
No whole-program compiler call-graph or artifact reachability theorem is claimed.

| Source call(s) | Caller path and operand | Provenance | Initial status |
|---|---|---|---|
| crates/aspis-statement/src/logup.rs:200,213 | semantic_oracle.rs:171 helper → pair_forest_trace.rs:636 rows → build_copy_logup_helper; chi minus compressed tuple, only nonzero weight | witness-derived + challenges lambda,chi | OPEN: native static/dynamic slot association and original pole event |
| crates/aspis-r1-cost-probe/src/host_sumcheck.rs:30 | host_semantic::build_with_helper_mode → prove_sumcheck → interpolate; product over j!=i of i-j for i,j<28 | public, despite witness-derived interpolated values | nonzero algebra obligation; no probabilistic exception needed |
| crates/aspis-core/src/circle.rs:40 | SemanticTranscript::challenge_reference_circle_point → sampler::circle_sample → secure_ood_circle_point_from_parameter → secure_circle_point_from_parameter; 1+t² | challenge from raw FS answer | zero at ±i, explicit fallback; challenge-input joint law remains L2, not witness operand |
| crates/aspis-core/src/transcript.rs (circle fallback helper; exact sites in candidates.json) | circle_sample fallback | fixed public parameter selected by row | fixed nonzero argument obligation |
| crates/aspis-core/src/field.rs:1019,1011,398 | QM31 inv wrapper → try_inv → CM31 norm inv → M31 norm inv | inherited from caller | field norm nonzero at nonzero canonical input; internal zero predicate branches also observed |
| crates/aspis-core/src/field.rs:213/1004 | base and extension entry kernels | inherited | all reached caller families must discharge preconditions |
| crates/aspis-core/src/r0/scalar.rs:46,61,63,75,80,92,99 | CodeField M31/CM31/QM31/WideExact inverses; norm descent | inherited | include when called from certificate geometry/reference; NOT infer every generic R0 prover is reached |
| crates/aspis-core/src/field/wide_exact.rs:155 | inherent WideExact inverse norm | inherited | conditional tower obligation; direct deployed-prover call still to establish |

## Certificate route outside crates

`prover::public_check` → z4/z9e.rs::p_r1_check → public_data, emit,
convert, extracted_builders, c3/check. These receive R1PublicChallenges only;
prior transcript/coupling association remains substantive. They do not receive
compiled witness or semantic columns. C3/build and C3/check have no inversion
call; certificate inverses are supplied and checked by multiplication.

| Source | Operand / provenance | Source guard or obligation |
|---|---|---|
| z4/z9c.rs:42,121 | M31 v[i], challenge-derived matrix pivot | v[i]==0 continues before invm |
| z4/z9c.rs:42,304 | M31 a[c][c], challenge-derived inverse-matrix pivot | find nonzero row, then swap(c,p); prove selected value retained |
| z4/z9c.rs:335,336 | fixed 2; alpha[9]-half, challenge-derived | 2 nonzero; half pole returns None/reject, not a witness read |
| z4/z9b.rs:51,59,108 | fixed 2,4 | nonzero constants |
| z4/z9b.rs:71–73 | x,y,z or doubles from line_inverse(query,depth), public indices | domain-coordinate nonzero; no witness operand |
| z4/z9.rs:298,299,316–320 | stored fibre and line x,y,z, public queries | domain-coordinate nonzero |
| z4/z9.rs:395 | fixed 2 | nonzero constant |
| z4/z9.rs:832,894 | reduced vector pivot, challenge-derived | nonzero selection before inverse; caller reach review required |
| z4/probe.rs:530 | fixed 2 in raw_c auxiliary algebra | nonzero constant |
| z4/probe.rs:2291,2292 | fixed 2; alpha[9]-half in tail_row | challenge-derived half pole returns None |
| z4/probe.rs:1282 | product of differences for fixed interpolation support | public indices; distinguish trial-only callers |

## Exclusions and negative edges

`host_commitment::EncodingDomain::encode` calls phi_inverse, which has NO
inversions; do not confuse it with r0/fold::phi. S2 `Variant::coefficients`
is a permutation, with NO NaturalBasis inversion. `Weights::new`, round,
fold and materialize do not invert. `prove_from_semantics` never calls
r0/prover::prove nor quotient/chord interpolation. The certificate route may
use generic geometry, but the native quotient prover in r0/prover.rs:258 is
not an edge from this prover. Its witness-bearing numerator does not make its
challenge/public line denominator witness-derived in any case.

`logup.rs:137,145,168,179` belong to the main/range helper, not the reached
copy helper; :364,367,378 are test-only forgery search. Most hits in
state_only_hiding_rank, r16/r17/v5/v6/v8 rank/proof experiments, core circle_fri
and examples/tests are alternate protocols or audit-only tests, not this
S2 route. `state_only_hiding.rs:1445` is in its test module; deployed mask
material construction has no inversions. Registry construction used here does
not call atomic_state_only_registry's matrix-elimination helper. Core build.rs
inverses generate public tables at build time, not a witness execution.

Residual inventory audit: resolve the transitive z4/probe utility reachability
and every generic function-pointer inverse; lexical absence alone is insufficient.
