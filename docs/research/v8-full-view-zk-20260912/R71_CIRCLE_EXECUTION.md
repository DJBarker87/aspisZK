# R71: complete extracted circle-map execution

Base revision: `bf9e352530094780724cb34648a80526befe6767` (R70).
Branch: `research/v8-r64-guarded-m31-20260929`.

## Proved boundary

For **every canonical four-limb input** `t`, the exact generated
`secure_ood_circle_point_from_parameter t` returns the encoded result of
`SamplerCirclePolicy.pureMap (decode t)` inside `Aeneas.Result.ok`.
Its public extraction entry has the same theorem. No arithmetic success,
inverse correctness, denominator nonzero, or no-failure premise is assumed.

The theorem distinguishes the protocol's returned errors from an internal
execution failure:

1. `1+t*t = 0` returns `SingularParameter`, before any subfield rejection.
2. A nonsingular parameter in CM31 returns `ParameterInCm31Subfield`.
3. A parameter outside CM31 returns exactly the retained rational-map point.
   The retained tower theorem supplies the nonzero denominator.
4. Every successful output has canonical coordinates, decodes to that point,
   and satisfies `x²+y²=1`. Internal `Result.fail` is excluded on all canonical
   inputs, including the two protocol-error paths.

The implementation is unchanged. This closes the circle-map source-execution
obligation, **not the transcript sampler or full privacy/soundness**.

## Reuse and source binding

`CircleScalarTransport` proves 20 facts. Generated scalar functions, including
the inverse-loop body/loop, are related to the R66 source by explicit equality
lemmas. Existing canonical arithmetic, word bounds, and inverse facts are then
reused; no inverse recurrence or nonsquare certificate is recomputed.

`CircleFieldExecution` proves 15 facts. It reuses the R66 raw product bounds and
exact norm algebra for the R69 CM31 kernels and QM31 inverse, and proves the
source square/add/sub operations used by the circle caller.

`CircleSourceExecution` proves 13 facts. It composes those operations with R70's
actual generated QM31 product, the extracted `Option::ok_or`, and the full
cached runtime's `Result`/`Try` control flow. It includes the CM31 equality test,
ordinary circle map, OOD map, entry function, successful-output properties and
exclusion of internal failures.

All declarations refer to the unchanged R69 generated functions. No R68
replacement iterator/array model is used. The evidence checker recursively
checks the R70/R69 source audits, generated-source pins, new proof-source pins,
transitive local dependencies, retained runtime objects and final compilation
metadata. The runner's inherited R66 preflight is support evidence, not itself
a check of R69 source binding.

## Compilation and audit

Three smallest-leaf checks followed by one final three-leaf replay; 316 cached
targets reused. Lean `leanprover/lean4:v4.32.0`, `lake env lean -j1 -M4500`, full
cached Aeneas runtime. The NUC cgroup enforced `MemoryHigh=5 GiB`,
`MemoryMax=7 GiB`, `MemorySwapMax=0`, `TasksMax=128`.

| Exact target | Exit | Wall seconds | Peak RSS KiB | Swaps |
|---|---:|---:|---:|---:|
| `AspisV8R19/CircleScalarTransport` | 0 | 1.79 | 3,699,156 | 0 |
| `AspisV8R19/CircleFieldExecution` | 0 | 2.33 | 3,709,084 | 0 |
| `AspisV8R19/CircleSourceExecution` | 0 | 2.14 | 3,704,732 | 0 |

All **48** `#print axioms` results contain at most `propext`, `Classical.choice`,
and `Quot.sound`. No new axioms, admitted proofs or raised heartbeat limit.
The first circle-leaf attempt failed only on ambiguous constructor names in
two `change` expressions. Explicit constructor qualification fixed it; the
failed log is retained and is not release evidence. No OOM occurred.

Audit command:
`python3 docs/research/v8-full-view-zk-20260912/tools/check_r71_evidence.py`.
Receipts, logs, source/dependency pins: `evidence/r71-circle/`.

No Rust or SBF change means no unchanged runtime suite was rerun. Retained
complete verifier CU: **1,495,663 / 1,497,050**; both actual 1M-cap runs still
exhaust. This milestone claims no CU saving. Selected ELF remains
`412c762bb5a0190bd7f068b12fb1323e8ba84985a727b1008fe30f29550dc518`.

## First remaining source proposition

Establish execution correspondence for the **actual transcript**
`challenge_qm31` and `challenge_secure_circle_point` with the retained bounded
sampler model. It must preserve all of:

- four canonical limbs, little-endian word decoding, masking, rejected-P
  consumption and block rollover;
- the eight-attempt per-limb bound and three-attempt circle bound;
- immediate propagation of inner `ChallengeSampleExhausted`;
- advanced transcript state after each rejected successful parameter;
- final `ParameterSampleExhausted` and the exact shared-oracle observation trace.

The current wrapper/model laws already preserve traces under their definitions;
they are not a generated-source theorem for these Rust loops. R71 must not be
used to relabel that remaining correspondence as complete, nor to assume fresh
independent random answers on known shared-oracle inputs.

Further full-view gates remain: seed expansion, C2 commitments, the joint
semantic/point/OOD/final/opening observations, visible failures, retries and
publication, justified numerical loss, and coherent pre-beta quotient-pair
extraction for soundness. C1's negative regression, fixed-block hiding and local
joint coverage remain separate and unchanged. This is not a verified compiler
or full privacy/soundness release. No merge, deployment or wallet operation.
