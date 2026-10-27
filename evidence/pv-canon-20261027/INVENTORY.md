# V403 producer inventory — stage 1

Source base ea81432954 (codex/pv-canon-20261027). No implementation changes.

The deployed R0 prover call is `crates/aspis-r1-cost-probe/src/host_sumcheck.rs:73`.
`prove_sumcheck` creates 28 coefficients with `interpolate` (line 12), and reads
its challenge from `SemanticTranscript::semantic` (r1_wire.rs:248), which calls
`sampler::qm31_sample` (sampler.rs:49). This is a base-P digit sampler, NOT the
legacy Transcript rejection sampler. Native hash bytes may be arbitrary: the
canonicality proof must quantify over every 32-byte block.

| Producer | Required invariant / current status |
|---|---|
| M31 raw constructor | No unconditional invariant; prove bounds at each construction. Sample/i/j indices are <28. |
| reduce_u64 | Two folds and subtract; prove for all u64, including maximal raw input. |
| M31 add/sub/neg | Preserve <P on canonical arguments. |
| M31 mul | reduce_u64 output; raw u32 multiplication fits u64. |
| inv/square_n | Canonical on every successful return; zero failure is separate V380. |
| CM31/QM31 constructors | Componentwise predicates; no implicit validation. |
| CM31/QM31 arithmetic | Compose base operation closure, including specialized square/mixed multiplication. |
| Interpolation | zero-initialized arrays; bounded constructor indices; arithmetic closure; successful inverse returns. |
| Oracle values | Native installed caller P: every successful oracle return is canonical; bind exact host_semantic arithmetic producers, not arbitrary callbacks. |
| Semantic challenge | qm31_div_pass remainder `% P`; qm31_digits repeats four times. semantic/update/sample_block failures produce no op121 call. |
| M31::from_le_bytes | Successful branch has v<P. |
| QM31::from_le_bytes / wire decode | Four successful M31 parses; high WideExact half checked zero. |
| Legacy Transcript::challenge_qm31 | masked word ≤P, reject equality P; all four accepted limbs <P. |

Other op121 calls: core state_only_sumcheck streaming verifier uses checked
round decode and legacy challenges; v6_transcript.rs:455 uses its checked compact
semantic decoder and legacy challenges. Prover state_only_zerocheck.rs is marked
unwired scaffold; v6_onefold_prover.rs is a distinct legacy path. Calls in tests,
v5_sumcheck_mask, state_only_hiding_rank and sim.rs require separate reachability
classification, not an assertion that they are the deployed host call.

The installed records caller on codex/pv-runjoin-20261026 remains a P6 candidate:
`evidence/pv-runjoin12-20261027/route.json` reports no accepted shipped records
extraction. Its native association cannot be assumed or added to T. T stays the
three PV_RunJoin_TrustItems fields.

Stage 2 correction: existing `PV_Join_CurrentPolynomialCanonical5.polynomial`
is stronger than a canonical-input interpolation result: successful current
interpolation is canonical even for arbitrary raw input values. Its scaling
uses multiplication/reduction before addition. Thus P_oracle is useful for the
whole field invariant but is NOT necessary for the op121 coefficient domain if
this exact current installation is the installed deployed dictionary. The
installed dictionary association itself remains P_installed.

Workflow correction (before ID 44221): the initial private runner recorded its
reservation after copying the new proof source. The scopes themselves were
always reservation/barrier capped. The runner now records admission before
any source scp, as local-lean rule 7 requires, and retains each attempted source
snapshot. No shared source was written during the initial runs either.

## Frozen deployed stack and input checks

At the frozen worktree source: `prover.rs:159` calls
`host_semantic::build_with_material`; this reaches
`build_with_helper_mode` and the sole op121-driving
`host_sumcheck::prove_sumcheck` invocation at host_semantic.rs:151.
The oracle is exactly the closure at lines 155 onward:
`point_claims` → `public.terminal_qm31` and selected-mask evaluation →
`mask.add(eta.mul(terminal)).add(extra(&dc,point[8],point[9]))`.
The `prover` feature gates host_sumcheck/host_semantic in lib.rs:32–33.

`host_semantic::build_with_helper_mode` explicitly rejects c1 columns of wrong
length or limbs ≥P, and rejects d/g values that fail a QM31 serialization/parse
roundtrip. It does not justify a universal invariant on every externally
supplied h1-padding value by its type alone. For op121 coefficients the
strong successful-interpolation canonicality theorem avoids assuming an
oracle-output invariant. The separate stronger claim that *all earlier field
values* in the prover are canonical would still need the padding/native-input
producer binding; it is not silently inferred here.

## Checked composition stage

44238–44240: sampler, polynomial, and generic semantic canonicality pass.
44248–44252: update/read equality, current sampler/semantic instantiation,
`PV_Canon_Prefix.op121_arguments`, proof-only monitored round definition and
successful-bind congruence pass. The prefix theorem assumes only the actual
source return equations and round<10, not a canonicality conclusion, an oracle
range premise, or an entropy law. Its dictionary is exactly
`PV_Join_PublicCaller.selected base ops`.

The stronger one-round instrumentation equality is being checked. Initial
44253 failed on simplifying a let-pair before matching the semantic Result;
no source/domain statement was weakened to resolve that elaboration issue.
