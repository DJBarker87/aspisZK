# Share five public gamma dots, retain independent outputs

Research continuation of `081e23f75ae40942234ffd848acf2910d7c929c1`,
2026-09-09. The previous goal turn made measured progress; this implements its
specified next experiment. No production/main/default or transcript change.

## Retained complete-transaction result

| Shape | Previous maximum | Shared-gamma maximum | Difference from same-pool selected V7 |
|---|---:|---:|---:|
| Transfer, current page | 1,050,628 | **1,025,815** | **−15,008** |
| Transfer, rollover | 1,063,414 | **1,038,559** | +4,158 |
| Withdrawal, current page | 1,068,895 | **1,044,027** | +7,662 |
| Withdrawal, rollover | 1,081,936 | **1,057,043** | +8,159 |

Identical maximum-body proofs save **24,813–24,911 CU each**. All transactions
declare the actual **1,200,000 CU TxV1 cap**. Worst-observed headroom is
**142,957 CU**. Current-page transfer is below the selected V7 control, but the
other three shapes are still above it. Fixture maxima do not establish an
all-input CU bound or complete V7 parity.

All 24 maximum-body cases, 24 ordinary-body cases and two post-real-verifier
failing-Token-CPI rollback controls pass. Proof identity, outcomes and protected
accounts are compared against the previous implementation. Successful executions
retain the same pinned Pool, Registry and Token3.5 SBF. Rollback uses the
intentional failing Token double **after actual V8 verification**. Unsupported
rollover stale/replay scenarios are not counted.

Selected ELF: **1,007,416 bytes**, **4,896 bytes smaller**, SHA256:

```text
8540f1abb5ca393500058323aec1b9212375159ca1de87e8fbfeede5319bd958
```

[Machine-readable results](shared-gamma-results.json) and the
[auditor](experiments/audit_shared_gamma.py) contain every per-proof delta,
source/artifact pin, resource measurement and axiom audit.

## Actual source and timing

The selected structured `prepare` used five independent `qm31_dot` calls with
the same `[1,gamma,...,gamma^28]` vector: point rows `v[271..300]`,
`v[300..329]`, `v[329..358]`, then OOD vectors `v[359..388]` and `v[388..417]`.
Those inputs are already canonically parsed. The first power is one by the
actual constructor, which initializes the table to ONE and writes indices1..28.

[`shared_gamma.rs`](experiments/shared_gamma.rs) takes exactly the 28 nonconstant
weights and five separately typed `[K;29]` rows. Its specified output for each
row is `row[0] + sum_j weights[j]*row[j+1]`. It does not test for gamma=1, assume
other powers are nonzero/nontrivial, or assume any helper/claim is honest.

Seven four-weight blocks are prepared once each and reused across the five
rows. Each row has its own nine raw channels and independent outer accumulator.
Every inner channel starts at zero and holds four canonical products. Each
chunk undergoes a partial Mersenne fold; the outer sum is seeded with the first
row value's literal four-limb constant injection. One final selected QM31
reconstruction completes each output.

This differs materially from the rejected runtime gamma-one guards in the
authenticated query loop: it exploits a **structural gamma^0 coefficient** in
five ordinary/OOD dots and shared decomposition, with no input-dependent guard.

No causality boundary moves. C1, early lambda/chi, adaptive C2, semantic rounds,
point claims, both sequential OOD absorptions and gamma remain as before.
`prepare` still absorbs inactive, derives kappa, and only then computes these
public deterministic values. The same three kappa-scaled outputs feed the
ordinary claim; the same two OOD outputs feed the interpolant. The functional
description and ordinary scalar are unchanged before tau. No response or
challenge is requested during or between the five arithmetic outputs.

The carried image gate, shifted ordinary rows, degree-q query batch, later
relation responses, authentication, terminal equality and actual Pool settlement
are untouched. The original five dots are not replaced by one weaker scalar
check: all five outputs remain independently equal to their references.

## Literal operation and range inventory

Before compiler simplification, the five generic dots decomposed 145 weights
and 145 values. The fixed kernel decomposes **28 weights and 140 values**, with
140 rather than 145 QM31 products. The old >16-element dot path makes
`5*(8*9+9)=405` explicit full M31 reduction calls in its chunk/outer stages.
The new path makes **20** final reduction calls and **360** partial folds
(315 inside seven chunks, 45 in final reconstruction). Canonical preparation,
integer additions, masks/shifts, constant injection and loop/buffer work remain
real costs; the complete measurement, not this inventory, decides the winner.

No new heap allocation is used. The source working arrays contain five
nine-u64 outer channels (360 bytes), four prepared weight decompositions
(144 bytes), and one nine-u64 raw row (72 bytes), plus temporaries. These are
source array sizes, not measured peak stack or allocator savings.

For `m=p-1`, every inner prefix is at most `n*m^2`, `n≤4`, strictly below u64.
Each raw chunk is below u64, so its partial fold is at most `5*p+3`. The
seeded outer prefix after `n≤7` chunks is at most `4*m+n*(5*p+3)`, whose
maximum is **83,751,862,250**, also below u64. The final reconstruction is copied
literally from the already-selected arbitrary-u64-safe partial-channel kernel.
The auditor checks the copy against `semantic_carry.rs`.

## What Lean proves

[`SharedGammaDots.lean`](experiments/SharedGammaDots.lean) imports pinned
SemanticCarry, AffinePrimal and QmCrossRange results, and proves the new
source-shaped composition:

| Interface | Established result |
|---|---|
| Canonical preparation | Literal modular Nat limb sums cast to the selected QM31 channel decomposition |
| Raw products | Casting each natural product channel yields the literal field product channel |
| Inner accumulation | Four canonical products and every wrapping prefix fit u64 |
| Partial reduction | Each partial fold preserves its field cast; adding partially folded chunks preserves the outer field value |
| Outer accumulation | Every seeded seven-chunk prefix fits u64 |
| Reconstruction | `one_group` and `kernel_result` connect actual raw product groups/partial folds to the list of QM31 tower products |
| Constant seed | Existing literal injection/cast theorem gives row[0]; structural unit theorem justifies gamma^0=1 |
| Group/index order | Generic four-way grouping plus the concrete `4*g+j` / `1+4*g+j` bounds and quotient/remainder identities |

`kernel_result` does not assume an opaque kernel-correctness equality, a valid
witness, provider success or zero residual. The five outputs instantiate the
same independent-row theorem. This is **kernel-checked source-shaped arithmetic
and integer-range reasoning**, not a full Rust/LLVM/SBF translation. The actual
Rust representation, bit-operation lowering/reduction and array traversal retain
their explicit source/refinement boundary; no tiny numerical assumption is
assigned to it.

## Executed evidence and resource discipline

The selected optimized Rust gate checks arbitrary independent five-row inputs,
all-maximal canonical weights/values, zero and one gamma, each of 580 row/index/
limb basis cells, and equality with both generic dots and naive multiplication.
An initial preflight accidentally overwrote its all-maximal weights in the
gamma-profile setup. The final v2 test fixes that case and compiles the actual
structured integration cfgs. Only this corrected source is SBF-measured.

| Focused job | Exit | Wall | Peak RSS | Swaps |
|---|---:|---:|---:|---:|
| Missing QmCrossRange olean refresh | 0 | 9.69s | 2,912,256,000 bytes | 0 |
| Final new Lean leaf | 0 | 1.85s | 2,908,192,768 bytes | 0 |
| Selected optimized Rust gate | 0 | 22.55s | 515,176 KiB | 0 |
| Quiet SBF build | 0 | 34.01s | 593,968 KiB | 0 |

The dependency refresh was necessary because its imported olean was absent.
The source is unchanged, and its rebuilt source/olean hashes are now pinned;
no package replay ran. The initial combined log exits1 because the following
new leaf used reserved syntax and an untargeted sum rewrite. The dependency
stage itself completed successfully. A second leaf exposed a rewrite mismatch
between two definitionally equal prime names. Explicit congruence fixed it.
The later concrete raw-product bridge needed a targeted fold induction rather
than recursive `simp`. Failed leaf logs (v1/v2/v4) are retained and excluded
from the final claim; v3 was a passing predecessor, v5 is the final endpoint.
No memory-pressure retry or enlarged cap occurred. All fifteen final audits
use only standard propext/Classical.choice/Quot.sound, with no `sorry` or new axiom.

The pinned cached-Mathlib workflow uses Lean4.32.0; source/olean provenance is
checked. Build scopes use High5/Max7GiB/jobs2, SVM High3/Max4GiB, all SwapMax0.
HostRust1.94.1, SBF tools1.54/checked Rust1.89-dev,
LiteSVM0.16.0/runtime4.2.1 are unchanged. Direct r10 offsets remain≤4,096,
with no new stack warning; this is not a whole-machine stack theorem.

## Reproduction and next decision

```sh
python3 docs/research/v8-no-work-100-20260907/experiments/audit_shared_gamma.py
bash docs/research/v8-no-work-100-20260907/experiments/run_shared_gamma_lean.sh NEW_LOG
```

On the authorised pinned NUC task COPY, apply `shared-gamma-callback.patch`
and `shared-gamma-structured.patch` against 081e23f7; add the kernel and updated
runners. Run the source guard, `run_shared_gamma_nuc.sh NEW_LOG`, then
`run_complete_build_nuc.sh shared-gamma NEW_LOG`. Run the complete matrix in
`shared-gamma` mode for maximum and ordinary fixtures, retaining the same Pool,
Token3.5 and actual 1200000 env cap. The driver CLI remains1400000 to avoid the
old diagnostic override. For rollback omit successful Token overrides, set
`ASPIS_V8_SHARED_GAMMA=1`, and run the rollback runner. Old named controls require
their archived source pins, not today's changed files.

Body census is still `697*16+52+24+22*621+2*296*26=40,282`. No extra public
message, field, nonce or transcript byte. Zero grinding security credit. There
is no new prover-time/peak-memory result, universal CU bound, full-view ZK/FS/
recovery certificate, or complete matched-V7 parity claim.

**Next bounded experiment:** in the authenticated query gamma kernel, C1's
four mixed-field dot results are canonically reduced and then added to a
three-product QM31 helper sum. Test transporting those still-bounded four raw
C1 sums into the helper's nine raw channels and reconstructing once. This
requires a new range bound for a wider constant seed, preserves every canonical
leaf check, and must include malicious/maximal inputs. It is not the rejected
C1 loop-layout fusion or gamma-one guard. Keep it only if complete SBF improves;
otherwise retain the current winner. The remaining measured V7 gap is small
enough that this specific repeated-reduction target may now be decisive.
