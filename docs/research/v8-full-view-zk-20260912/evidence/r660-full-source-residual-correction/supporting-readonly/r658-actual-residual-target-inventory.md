# R658: actual residual desired-target inventory

Scope: read-only map for the R657 premise
`evalSeven desired alpha = 0`. This is an inventory, not a source
correspondence or privacy conclusion.

## Frozen R117 source

The frozen selected source revision recorded by R550 is
`6677d5f1310ff7373301fbd79f186278f772e68a`. The NUC frozen tree is
`/home/dombarker/project-offloads/aspis-r20-r117-primal-20260930-a`.

| Role | Frozen path and SHA-256 | Exact lines |
|---|---|---|
| Selected verifier suffix | `docs/research/v8-no-work-100-20260907/experiments/r17_host_relation.rs`, `3b7a5040509e0c3ad5e421e49a4f6d1d106c5adabfc2bf891bf8685c66b4b801` | 446–521 |
| Owned first-fold implementation | `docs/research/v8-no-work-100-20260907/experiments/r17_owned_primal.rs`, `4c4dca09aee38d16bdd2ff39d8c841b973cd44cd2f232061ee173b0caa131a56` | 1–15 |
| Fixed-prefix H1 correction audit | `docs/research/v8-no-work-100-20260907/experiments/r17_c1_witness_audit.rs`, `1aa5c416fd971bb65bf5fd7aab20046a6e13c171dbaf272674337682f57f1a13` | 1–68, 71–105 |

`verify_cached` samples `beta` at lines 447–450, takes `w.v[443..699]`
as Final256 at line 461, runs the query schedule at 462 and opened channel at
464, samples `alpha[1..3]` and folds Final256 at 476–480, and consumes the
four remaining values in the terminal check at 485–515. The initial alpha is
sampled at 455–460. Its inner fold is `r117_retained_fold` in
`r17_owned_primal.rs:3–12`: each output is the alpha-weighted four-entry
block, then the vector is truncated by four.

The audit constructs the requested ordinary target shape, but it is explicitly
a *fixed-prefix C1 witness-offset correction* (`r17_c1_witness_audit.rs:1`),
not a selected verifier execution path. It has no beta argument. Its names
are `rq` and `q`, rather than `rq_base` and `q_H1`:

- lines 8–10 set `scale = p.gamma.pow(26)` and scale the base H1 data;
- line 24 makes `rq` from the decoded C2 values; line 28 computes its
  `finals = primal(&rq, alpha)`;
- lines 38–47 build the affine H1 matrix, with Final256 constraints in
  rows 306–561 from `primal(&q, alpha)`;
- line 51 sets the 256 Final256 target entries to
  `- finals[i] * scale.inv()`;
- line 65 forms `total[i] = rq[i] + scale * q[i]`, and line 66 asserts
  all `primal(&total, alpha)` values are zero.

Thus the audit demonstrates the intended algebraic target expression
`rq_base + gamma^26 * q_H1` and its first-fold zero check for one fixed prefix.
It does not show that every legal same-public witness difference produces
that target, or that this audit construction is an actual verifier callback
stage before beta. In the selected suffix beta is already sampled at line 448.

Opened/Final256 constraints also occur in audit lines 61–66: the corrected C2
code is zero for each selected query fibre; it has zero point and OOD values;
and the combined `total` has all 256 `primal` values zero. The selected
verifier separately uses its submitted Final256 slice at 461 and authenticates
opened values through `opened_channel` at 464. No existing source theorem
connects those two representations for arbitrary legal same-public witnesses.

## Existing Lean definitions and exact reusable facts

| File (SHA-256) | Definition or theorem | What it supplies |
|---|---|---|
| `lean/AspisV8R19/R370KernelEvaluation.lean` (`8e3d859d346778bcbb2a595ef85895bb9454e8a4f976bda0bb31c7d10d289b71`) lines 11–16, 70–75 | `firstFold`; `kernel_eval_zero_of_first_fold` | Defined four-slot alpha fold and zero kernel evaluation from pointwise first-fold zero. It is an exact-field model, not `owned_primal` source execution. |
| `lean/AspisV8R19/R655SourceResidualCompletion.lean` (`b93260112ac4a1323009467dbc8241b6e03df00b11b3e07ffbb527d3de0fba90`) lines 13–22 | `source_relation_eval_zero` | First-fold-zero of a supplied `q` gives `evalSeven` of its seven source relations equal to zero. |
| same, lines 27–53 | `ordinary_source_completion`, `structured_source_completion` | Uses explicit alpha, first-fold, selected coefficient, and structured-moment premises. |
| `lean/AspisV8R19/R657CompleteResidualRepair.lean` (`0c71a7655177cbedbb2d44bc82a38f96cf05af16d42027342cc7d94b9c943ec4`) lines 13–25, 80–86 | `repairTarget`; `complete_residual_repair` | Requires `evalSeven desired alpha = 0`; it does not derive it from a witness difference. |
| `lean/AspisV8R19/NormalizedQuotient.lean` (`79545a432180667215d95e31419945b0079c88a7388ca8353e20540c37bc5b9a`) lines 32–39, 63–103 | `quotient_fold`, `quotient_final_zero`, `final_zero_of_coefficients` | Model fold/root/final-zero facts for normalized quotient directions, under their stated conditions. |
| `lean/AspisV8R19/R524FinitePreparedFold.lean` lines 42–65 | `family_prepared_final_zero` | Model prepared final zero for finite directions, retaining circle, inverse, and line nonzero conditions. |
| `lean/AspisV8R17/ChannelResidual.lean` lines 27–54 | `channel_residual_identity`, `claimed_channel_residual_identity` | Generic two-channel residual algebra. Its comments expressly retain source refinement and extraction as separate. |
| `lean/AspisV8R17/HelperAffine.lean` (`8864289661f4cce8324a1c9f8e223478146bbbc232e791eb612a5c07787890f5`) lines 10–39 | `helperTerminal_difference`, `horner_start_difference` | Abstract helper and lane affine differences only; no binding to the selected H1 construction above. |
| `lean/AspisV8R19/R154QueryScheduleBridge.lean` (`1a61f7fa8ba512bbf0dfd11aa0f152e8ae1113dc22873d08a41cd224f570ea6c`) lines 38–60 | `sourceChronology`, `source_chronology_exact` | Query schedule/Final256 transcript ordering, not the arbitrary witness target or opened Final256 equality. |

## Missing bridge, stated mechanically

There is no theorem found that takes an arbitrary legal same-public old/new
witness pair, identifies a selected source residual `desired` with the seven
ordinary coefficients induced by the frozen `rq + gamma^26*q_H1` construction,
and proves its `evalSeven desired alpha = 0`. There is also no theorem found
that ties the audit's `primal(&total, alpha)`/Final256 assertions to the
selected `verify_cached` submitted slice, authenticated openings, and alpha
fold implementation for every accepted run.
