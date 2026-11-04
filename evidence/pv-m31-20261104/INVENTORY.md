# V403 caller and producer inventory — stage 1

Candidate: `d4ed1ba89f05a754d3982b9250f53acbd405ce7b`, the explicitly
requested snapshot of `codex/cx-prover-rw-20261023`. The branch now points
elsewhere; this inventory never follows its moving tip. Research/worktree
base: `61684cb2251381c897e112c85e48f092a82f5d31`.

This is a source inventory, not a reachability or closure certificate.
`inventory.py` reads immutable Git objects and records source SHA-256 values,
every direct call expression and enclosing function in `inventory.json`.
Search roots: `crates/`, `programs/`, `tools/r1-cost-probe/`. Historical copies,
reference harnesses and evidence snapshots outside these roots are not
additional application call sites. No aliased function-pointer reachability
claim is made by this textual census.

## Direct non-test call sites and immediate producers

Paths below are relative to the candidate. Counts: **18 direct call
expressions: nine non-test, nine test**. The nine non-test expressions occur
in eight functions. Only C1 is the host round of the assigned extracted-prefix
theorem; the other sites are recorded rather than silently identified with it.

| ID | Caller path:line / function | Coefficient producer | Challenge producer / domain |
|---|---|---|---|
| C1 | `crates/aspis-r1-cost-probe/src/host_sumcheck.rs:113`, `prove_sumcheck_round` | `interpolate:13`, called at :99; helper chain :22–53. Successful interpolation canonicality accepts arbitrary raw samples in the prior theorem. | `r1_wire.rs:248` semantic (declaration :261), called at host_sumcheck :111; point store/read :111/:113. Four base-P digits from sampler below. Requires round <10. |
| C2 | `crates/aspis-core/src/state_only_sumcheck.rs:279`, `verify_state_only_sumcheck_streaming` | `decode_state_only_polynomial:225`, called at :267, successful QM31 parser per coefficient | `absorb_state_only_sumcheck_round:244`, then `Transcript::challenge_qm31`, success only |
| C3 | `crates/aspis-core/src/v6_transcript.rs:455`, `verify_compact_semantic_sumcheck` | `V6FixedFieldStream::next_qm31` at :415/:426; concrete reader `v6_onefold.rs:282` rejects any limb >=P. Missing c1 at :441–447 via reduce_u64, :449 via sub. | `Transcript::challenge_qm31` at :452. Incoming running claim needs canonicality, and op121 output invariant is needed for later rounds. A generic stream trait alone does not guarantee its outputs. |
| C4 | `crates/aspis-prover/src/state_only_hiding.rs:1622`, `r0::prove_sumcheck` | local `interpolate:1561`, invoked :1611 | core `state_only_prefix.rs:1753` semantic, assigned point :1620. Feature `r0`. Distinct caller and sampler implementation, not C1. |
| C5 | `crates/aspis-prover/src/state_only_zerocheck.rs:126`, `prove_state_only_sumcheck_from_claim` | `interpolate_state_only:47`, called at :116 | `absorb_state_only_sumcheck_round` :123. Explicitly unwired payment scaffold (file header). Target switches with `prover` feature. |
| C6 | `crates/aspis-prover/src/v5_sumcheck_mask.rs:168`, `V5SumcheckMask::evaluate` | `round_polynomial:144`: stored sampled zero-boundary polynomial plus incoming_claim.half; `sample:79`, `sample_zero_boundary_round:41`, `v5_mask.rs:361` sample_qm31 | **Caller-supplied point** at :155. No unconditional canonicality fact follows from `QM31`'s Rust type. Module gated by `v5-mask` (`aspis-prover/src/lib.rs:55`). |
| C7 | `crates/aspis-prover/src/v6_onefold_prover.rs:1465`, `build_onefold_proof_with_pow_mode` | `interpolate_degree27:619`, called :1454 | legacy `Transcript::challenge_qm31` :1462, with errors propagated |
| C8a/b | `crates/aspis-r1-cost-probe/src/sim.rs:300,316`, `semantic` | host `interpolate` :297; final c0/c1 shift :310–311 through arithmetic | `Drawn.sem[15+i]` :251, filled through semantic sampling at :166. Feature guard `r1p-check` AND `insecure-spend-fixture` in lib.rs:29; this is the simulator path, not an honest prover call. |

Target selection matters: C1 imports
`aspis_prover::host_arithmetic::evaluate_state_only_polynomial` at
`host_sumcheck.rs:6`; its body is `host_arithmetic.rs:159–202`. C5 selects this
same host item under `prover` and the core item otherwise. The remaining listed
sites import the core evaluator (`state_only_sumcheck.rs:160–187`). V220's
restored core source/reference Result law is not, by its name alone, a binding
of C1 to the selected core-named op121 extraction.

## Test expressions (not deployment exclusions proved here)

* `aspis-core/src/state_only_sumcheck.rs`: :350 `valid_random_wire`, :413
  `radix_four_matches_horner_at_random_off_domain_points`, :427/:440
  `indexed_radix_four_matches_former_iterator_spelling`, under test module :310.
* `aspis-prover/src/state_only_hiding_rank.rs:9717`,
  `compressed_sumcheck_terminal_and_conditional_kernel_match_the_wire`, under
  `cfg(test)` :9683.
* `aspis-prover/src/v5_sumcheck_mask.rs`: :370
  `round_boundaries_chain_to_the_global_evaluation`; :452/:453/:454
  `masked_prover_matches_round_model_streaming_verifier_and_terminal`, under
  `cfg(test)` :238.

The earlier report's description of `state_only_hiding` as a test-only site
would be incorrect: C4 is in its `cfg(feature="r0")` production module.

## M31-producing paths into these arguments

All paths here start with `crates/` unless explicitly noted. Bounds refer to
the four **raw** u32 limbs, each <2147483647, never equality modulo P.

| Producer family | Candidate source coordinates | Required invariant / retained proof scope |
|---|---|---|
| Raw constructor / constants | `aspis-core/src/field.rs:19–23`, ZERO/ONE :54 onward; host_sumcheck :29/:42/:137 | `M31(pub u32)` is public and unchecked. Constructors need bounded inputs. Interpolation i,j<28; samples<28; ZERO/ONE canonical. Prior `PV_Canon_Constructors` proves the bounded facts, not arbitrary constructor canonicality. |
| CT reducer / base arithmetic | `aspis-core/src/field/ct.rs:7,12,18,26,30,34`; field.rs :3279–3291, mul :133, reduce_u62 :145, reduce_u64 :153, square_n :47, inv :213 | reduce64 output canonical for every u64; mul reduces even arbitrary raw u32 operands. add/sub/neg preserve canonical inputs; inversion preserves successful-output bounds. Prior `PV_Canon_{Reduce,MReduce,Mul,Add,Sub,Neg,Inverse}`; extraction/selected-source association remains explicit. |
| Tower construction / arithmetic | `aspis-core/src/field.rs:271,276,281–351,891,896–975` | CM31/QM31 construction is componentwise; no hidden validation. Scaling multiplies/reduces before interpolation adds. Prior `PV_Canon_{LiftC,LiftQ,CAdd,CSub,CMul,QAdd,QMul,QScale}` and specialized square/prepared modules. |
| Polynomial interpolation | C1 :13–53; C4 :1561–1593; C5 :47–92; C7 :619 onward | Distinct bodies, requiring their own transport. C1 old selected extracted theorem `PV_Canon.polynomial` proves all returned coefficients canonical even for arbitrary input samples; not an unconditional native binding of all four interpolators. |
| Host challenge sampler | `aspis-r1-cost-probe/src/sampler.rs:8` qm31_div_pass, :23 qm31_digits, :49 qm31_sample; `r1_wire.rs:200–231,261–266` | remainder `% P` <P, four quotient-preserving passes, raw M31 constructors at :52–53. Prior `PV_Canon.sampler_total` and `current_semantic` cover the selected extraction on arbitrary hash blocks. No entropy/distribution premise. |
| Core R0 challenge sampler | `aspis-core/src/state_only_prefix.rs:1753` semantic and its local qm31_sample import | Separate core R0 sampler binding is required for C4; same method is not identity evidence. |
| Legacy challenge sampler | `aspis-core/src/transcript.rs:409–448` | Each limb masks by P and rejects equality P. Success gives <P. Failed retry is retained. Prior `PV_Canon_LegacyMask` is a helper shape law, not a full native caller certificate. |
| Canonical parsers | `aspis-core/src/field.rs:239,410,1022`; state_only_sumcheck :225; v6_onefold :282 | Success only after bounds checks. Prior `PV_Canon_ParseM/ParseC/ParseQ` are extracted producer facts. Whole parser/caller transport is separate. |
| V5 mask sampling | `aspis-prover/src/v5_mask.rs:361`; v5_sumcheck_mask :41–92 | Source-sampled coefficients plus canonical arithmetic; supplied point in C6 still needs its own input domain. |
| Host oracle values | `aspis-r1-cost-probe/src/host_semantic.rs:103,139–143`; host_sumcheck :80–85/:117–143 | C1 interpolation theorem deliberately avoids requiring all oracle replies canonical. Stronger whole-prover invariants must bind these producers separately. |

## Transport children on the actual C1 path

With `r1p-check` plus `aspis-r1-cost-probe/ct-host-prover`, release/client
configuration (panic=abort for adopted client), C1 runs
`host_work::map(100+round,28*(1<<(9-round)), callback)` at :80.
The child is `host_work.rs:11–28`, using
`docs/research/v8-r0-zk-20261009/c3/check/src/native_workers.rs:26–61`.
It returns `Vec<Result<QM31,host_wire::Error>>`, not a guaranteed-success
canonical vector. Its ordered_families child reads/writes ACTIVE TLS,
spawns/joins scoped threads and retains panic/abort paths. The round then
uses merge_evaluations :117, interpolate :13, boundary_sum, encode_polynomial
:148, wire::record, transcript.semantic, output.extend_from_slice and op121.
The native caller certificate must retain each child's full reply and frame.

This list is committed before any new invariant or caller proof. It makes no
new theorem, row-closure, deployment or coherent-audit claim.
