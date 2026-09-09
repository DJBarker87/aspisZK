# Final-coefficient folds: move the constant inside reduction

Research continuation of `a955be1c158578057fed1840ed9f005cb3f1a18b`,
2026-09-09. The preceding goal turn made measured progress; this continuation
implements its specified next experiment. Production/main and all protocol
messages/checks stay unchanged.

## Retained complete-transaction result

| Shape | Previous maximum | Affine-fold maximum | Same-pool selected V7 excess |
|---|---:|---:|---:|
| Transfer, current page | 1,060,825 | **1,060,334** | 19,511 |
| Transfer, rollover | 1,073,615 | **1,073,105** | 38,704 |
| Withdrawal, current page | 1,079,103 | **1,078,592** | 42,227 |
| Withdrawal, rollover | 1,092,138 | **1,091,626** | 42,742 |

The identical twelve maximum-body proofs save **491–534 CU each**. The actual
TxV1 cap remains 1,200,000, leaving **108,374 CU worst-observed headroom**.
These are measured fixture maxima, not a universal bound or V7 parity.

All 24 maximum-body cases, 24 ordinary-body cases and two post-real-verifier
failing-Token-CPI rollback controls pass with unchanged outcomes, proof identity
and protected accounts. Successful cases use the same pinned Token3.5 SBF,
Pool and Registry. Rollback uses the intentional failing Token double after
the real V8 verifier, not an accepting-verifier shortcut. Unsupported rollover
stale/replay scenarios remain uncounted.

The selected ELF is **1,010,800 bytes**, 104 fewer than the preceding control:

```text
e8179c87beadc467a8aa3e9371e6d318890f361d29de7b6d8dd298190c690cea
```

[Machine-readable results](affine-primal-results.json) and
[the local auditor](experiments/audit_affine_primal.py) pin all per-proof
deltas, artifacts, source hashes, resources and proof audits.

## What actually changes

After all relation alphas are fixed, the selected structured callback folds
final256 to 64, then 16, then four coefficients. Every four-entry group used

```text
c0 + qm31_sum_products3_prepared([a,a^2,a^3], [c1,c2,c3]).
```

The research wrapper now calls the existing
`qm31_add_sum_products3_prepared(c0, powers, rest)` instead. It includes the
constant in the raw channels before their existing field reduction. The
prepared powers, three products, nine channels, source slice order, chunk
boundaries and output lengths do not change.

There are 64+16+4 = 84 groups. Four separate canonical M31 additions disappear
per group: **336 total**. The literal raw constant-injection expression adds
nine u64 additions per group before compiler common-subexpression elimination;
those operations are charged rather than described as free. There are no new
field products, reduction channels, heap allocations or challenge preparations.
The expected reduction work saving is not substituted for measured CU.

The actual input path is unchanged: the fixed-field parser canonically decodes
all 697 QM31 values; final256 comes from `w.v[441..697]`. Each subsequent fold
returns ordinary canonical field-operation results. A prover cannot supply an
unreduced machine limb through a new unchecked path. The helper is internal;
its use of `chunks_exact(4)` matches the old helper even for arbitrary private
lengths. In the verifier, the three lengths are exactly 256, 64 and 16.

## Literal algebra and range bridge

Write the constant's canonical base limbs as `(a,b,c,d)`. The affine kernel
changes just these four entries of its 3×3 raw channel matrix S:

```text
S[0][0] += a
S[0][2] += a+b
S[2][0] += a+c
S[2][2] += (a+c)+(b+d).
```

[`AffinePrimal.lean`](experiments/AffinePrimal.lean) models that literal
matrix update and the source's actual two-level reconstruction. Each CM31
row reconstructs `(s0-s1, s2-s0-s1)`; QM31 reconstruction uses the actual
`2+i` tower constant, followed by the c1 subtraction. `injected_constant`
proves that reconstruction changes by exactly `(a,b,c,d)` for **arbitrary
previous channel values**. It does not assume that the residual, constant,
proof or witness is honest.

`inject_cast` and `raw_injection_reconstructs` connect natural-number channel
updates to field casting/reconstruction. Thus this is not merely an opaque
assumption that the named fast kernel computes the old expression.

The machine-range side separately proves:

- Each unchanged three-product channel is at most `3*(p-1)^2` from its
  canonical factors, including prepared canonical limb sums.
- Every literal constant offset and intermediate nested sum is at most
  `4*(p-1)`. The source's nested wrapping additions equal integer addition.
- Every channel plus its offset is below `2^64`, using
  `3*(p-1)^2+4*(p-1)<2^64`. The final wrapping channel update is exact.

No new unchecked overflow assumption appears. The earlier `M31RangeKernels`
affine ceiling already anticipated this operation; the new proof connects the
actual four-limb offsets and all nine reconstructed channels. Its large-file
replay was not needed: only the new cached-Mathlib leaf was compiled.

This is **kernel-checked source-shaped arithmetic/cast/range reasoning**, plus
source inspection and actual-source differential testing. It is not a complete
Rust/LLVM/SBF translation. Canonical field representation, the selected
reduction implementation, Vec traversal and compiler lowering retain their
explicit source/refinement boundary. No new numerical error probability is
assigned to that boundary.

Compact response reconstruction, image weights, shifted ordinary rows, rho
injection, query/final matching, terminal equality, authentication, caller
binding and Pool settlement are untouched. The returned four coefficients
are used by the exact same final equality; no check is omitted on the basis
that an honest residual was zero.

## Executed evidence

The selected-arithmetic release test checks the actual affine function against
both the prior sum-plus-constant and naive QM31 multiplication on 4,096
arbitrary products, including all-maximal canonical factors/constant. It also
checks 256 complete three-pass folds, degenerate zero/one alphas and 15 private
chunk lengths, comparing every intermediate output with the Horner reference.
This is changed-kernel coverage, not a repeat of the earlier quotient test.

Final Lean leaf: exit0, **2.34s**, **2,909,470,720-byte peak RSS**, zero swaps.
All nine audits use only standard propext/Classical.choice/Quot.sound; no
retained `sorry` or new axiom. The initial focused leaf failed in 6.76s because
an annotation asked Lean to treat a Nat matrix as a field matrix instead of
casting it. Explicit Nat casts fix that elaboration error. The failed log is
retained and excluded from claimed proof evidence. No package replay ran.

Lean4.32.0 and Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`, cached
Tactic olean, final source and olean hashes are recorded by the runner/log.
The final source/olean hashes are checked by the machine-readable audit.

| Focused NUC job | Exit | Wall seconds | Peak RSS KiB | Swaps |
|---|---:|---:|---:|---:|
| Selected arithmetic release test/build | 0 | 22.25 | 518,256 | 0 |
| Quiet SBF build | 0 | 33.78 | 592,592 | 0 |

Compilation dominates. Build scopes use High5/Max7GiB/jobs2; SVM scopes use
High3/Max4GiB, all SwapMax0. HostRust1.94.1, SBF tools1.54/checked optimized
Rust1.89-dev, LiteSVM0.16.0/runtime4.2.1 and all surrounding programs are
unchanged. Direct-r10 accesses remain≤4,096 with no new stack warning; this
does not establish a whole-machine stack theorem. The three output Vec sizes
are unchanged; actual allocator/peak-memory delta is not inferred to be zero.

## Reproduction and next decision

```sh
python3 docs/research/v8-no-work-100-20260907/experiments/audit_affine_primal.py
bash docs/research/v8-no-work-100-20260907/experiments/run_affine_primal_lean.sh NEW_LOG
```

On the authorised pinned NUC task COPY, apply `affine-primal-callback.patch`
against a955be1c, add `affine_primal.rs` and the updated runners. The source
guard checks all six affected/dependent research files. Run
`run_affine_primal_nuc.sh NEW_LOG`, then
`run_complete_build_nuc.sh affine-primal NEW_LOG`. Maximum and ordinary
matrices use `run_complete_matrix_nuc.sh affine-primal NEW_OUTPUT` with the
same pinned Token environment, Pool selector and actual 1.2M cap. Add
`ASPIS_COMPLETE_MAX_FIXTURES=1` only for maximum-body fixtures. Rollback uses
`ASPIS_V8_AFFINE_PRIMAL=1 run_pool_zero_cases_nuc.sh rollback NEW_OUTPUT`
without the successful-Token environment. Logs retain the literal commands.

The Solana testing workflow kept the decision at matched complete transactions
and rollback. Retain the change: every measured maximum case improves, with
unchanged body/transcript/checks and a slightly smaller ELF. Body census stays
`697*16+52+24+22*621+2*296*26=40,282`. No new prover-time measurement, extra
search or positive grinding credit is claimed. Global recovery, full-view
adaptive privacy and resource-bounded FS keep their previous open status.

**Single next experiment:** fuse the semantic block-Horner carry with its
three-product sum. Its recurrence is
`a^4*acc + c0 + a*c1 + a^2*c2 + a^3*c3`; unlike this small constant-only
rewrite, a four-product affine accumulator could share reductions with the
carry multiplication as well. First prove the four-product-plus-constant
range and literal channel construction, then test the actual selected
arithmetic and complete quiet transactions. Do not assume the current
three-product bound covers a fourth product, or count any prospective saving
before measurement. Reject the control if integrated CU regresses or a new
range/canonicality obligation is unsupported. This is not a claim that all
safe optimisations are exhausted.
