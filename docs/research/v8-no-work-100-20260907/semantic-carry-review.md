# Semantic Horner carry: one reconstruction instead of two

Continuation of `66e39a53215f5bef341e58523230da9dd6adcf8e`, 2026-09-09.
Research-only, byte/transcript preserving. This is another measured improvement
over the already-structured verifier, not a comparison with the dense prototype.

## Retained result

| Complete transaction | Affine-primal maximum | Semantic-carry maximum | Excess over same-pool V7 |
|---|---:|---:|---:|
| Transfer, current page | 1,060,334 | **1,057,234** | 16,411 |
| Transfer, rollover | 1,073,105 | **1,070,020** | 35,619 |
| Withdrawal, current page | 1,078,592 | **1,075,506** | 39,141 |
| Withdrawal, rollover | 1,091,626 | **1,088,538** | 39,654 |

The identical twelve maximum-body proofs save **3,065–3,100 CU each**.
All transactions declare the actual **1,200,000 CU TxV1 cap**. Worst-observed
headroom is **111,462 CU**. These fixture maxima do not establish a universal
CU bound or matched V7 parity.

The 24 maximum-body cases, 24 ordinary-body cases and two post-real-verifier
failing-Token-CPI rollback controls pass with unchanged outcomes, proof identity
and protected-account checks. Successful transactions retain the same pinned
Pool, Registry and Token3.5 SBF. Rollback uses the intentional failing Token
double after real V8 verification. Unsupported rollover stale/replay scenarios
are not counted. [Results](semantic-carry-results.json) and the
[auditor](experiments/audit_semantic_carry.py) preserve per-proof comparisons.

Selected verifier: **1,010,688 bytes**, 112 fewer than affine-primal, SHA256:

```text
7842e538f9e132b5a16ab79af2113320e9927d9860685e5e8e2d8f3b0bcd85f8
```

## Exact change

For each degree-27 semantic response, the old evaluator used seven reverse
four-coefficient blocks. Each carried block separately reconstructed
`alpha^4*acc`, then added the constant and the three-product partial sum.
[`semantic_carry.rs`](experiments/semantic_carry.rs) seeds the constant into
the same nine Karatsuba channels, accumulates the **four** products, and
reconstructs once. The first block still has only three products.

Over ten rounds, there are ten initial three-product blocks and sixty carried
four-product blocks. Sixty separate carry reconstructions disappear. There
are no added field products or heap allocations; challenge-channel preparation
and low-level integer additions remain real costs included in the measurement.

The source path remains canonical parser → compact 28-coefficient polynomial
reconstruction → fresh alpha → evaluation → unchanged terminal check. The
coefficient order, omitted coefficient, alpha, transcript absorption, response
order, and final canonical field result do not change. The helper neither
assumes zero residuals nor skips a check. It accepts arbitrary canonical
coefficients, including malicious ones. Carried image, shifted ordinary rows,
degree-q rho batch, authentication and actual Pool settlement are untouched.

## Proof and machine-range interface

[`SemanticCarry.lean`](experiments/SemanticCarry.lean) proves the literal
3×3 channel product reconstructs the QM31 tower multiplication (`2+i`),
reconstruction is linear, and seeded accumulation equals the corresponding
list of field products. It consumes the previously proved four-limb constant
injection rather than assuming a fast-kernel specification.

For canonical base limbs `m=p-1`, every seeded prefix is at most
`n*m^2+4*m`, with `n≤4`. The new bound is
`4*m^2+4*m < 2^64`; each wrapping multiply/add therefore equals integer
arithmetic. Five products exceed this fresh-accumulator bound. The four-product
proof cannot be extrapolated to five terms or an arbitrary existing accumulator.

The actual partial-channel reconstruction is copied **literally** from the
selected `qm-channel-partial.patch`. The auditor checks that equality and pins
`QmCrossRange.lean` and its existing axiom logs at
`32026b0a1dc139f2684dd9dad247901d8d5ecdd2`. Its raw-u64 partial-fold,
positive/negative-prefix, modular-congruence and reconstruction lemmas apply to
arbitrary u64 channels, hence also these newly bounded channels. No unchanged
replay was necessary. The old logs predate embedded source-hash records; their
committed source/log identity is recorded explicitly, not invented retroactively.

The new Horner theorem proves the carried recurrence and its ordered list
composition; the initial-zero-carry theorem permits the three-product first
block. This is **kernel-checked source-shaped algebra/range reasoning**, not
a Rust-to-Lean translation. Canonical Rust representations, loop/slice lowering,
the final reduction primitive and LLVM/SBF remain explicit refinement boundaries.
No tiny numerical assumption is assigned to them.

## Executed checks and resources

The selected optimized Rust test covers arbitrary affine products, complete
degree-27 evaluations, basis coefficients, zero/one/maximal coordinates and
challenges, every maximal four-product prefix, and raw reconstruction including
u64::MAX channels. An earlier preflight used the slower nine-canonical-channel
reference; only the selected partial-channel version was SBF-measured.

| Focused job | Exit | Wall | Peak RSS | Swaps |
|---|---:|---:|---:|---:|
| New cached Lean leaf | 0 | 12.34s | 2,904,457,216 bytes | 0 |
| Selected optimized Rust gate | 0 | 2.59s | 206,776 KiB | 0 |
| Quiet SBF build | 0 | 34.13s | 592,892 KiB | 0 |

All ten new axiom audits contain only standard propext/Classical.choice/
Quot.sound; no retained `sorry` or new axiom. The runner verifies the imported
AffinePrimal source/olean and cached Mathlib provenance. No package replay ran.
NUC build scopes: High5/Max7GiB/jobs2; SVM: High3/Max4GiB; all SwapMax0.
Rust1.94.1, SBF tools1.54/checked optimized Rust1.89-dev,
LiteSVM0.16.0/runtime4.2.1 are unchanged. Direct r10 offsets remain≤4,096
with no new stack warning. This is not a whole-machine stack theorem.

## Reproduce and next step

```sh
python3 docs/research/v8-no-work-100-20260907/experiments/audit_semantic_carry.py
bash docs/research/v8-no-work-100-20260907/experiments/run_semantic_carry_lean.sh NEW_LOG
```

On the authorised pinned NUC task COPY, apply the callback and verifier
`semantic-carry-*.patch` files against 66e39a53; add the new kernel and runners.
`check_semantic_carry_sources.sh` pins the affected/dependent files. Run
`run_semantic_carry_nuc.sh NEW_LOG`, then `run_complete_build_nuc.sh
semantic-carry NEW_LOG`. Run `run_complete_matrix_nuc.sh semantic-carry
NEW_OUTPUT` once with maximum fixtures and once ordinary, with
`ASPIS_POOL_ZERO_FAST=1 ASPIS_COMPLETE_TX_LIMIT=1200000 ASPIS_TOKEN_CONTROL=legacy35`
and the pinned Token ELF directory. The driver CLI remains 1400000: the env
selects the real 1200000 declaration without activating the old diagnostic override.
For rollback omit the successful Token env, set `ASPIS_V8_SEMANTIC_CARRY=1`
and run `run_pool_zero_cases_nuc.sh rollback NEW_OUTPUT`.

Body census remains `697*16+52+24+22*621+2*296*26=40,282`. No new proof or
transcript bytes, and zero grinding credit. No new prover latency or peak-memory
measurement is claimed. Full-view ZK, resource-bounded FS, global recovery and
all-input CU coverage remain separate existing obligations.

**Next bounded experiment:** compact semantic reconstruction currently sums
26 canonical coefficients with reduction after each addition. Test a fixed-size
integer accumulation and one final reduction per limb, with the literal
`claim-2*c0-sum` boundary and every prefix proved in range. Keep it only if the
same-proof complete SBF matrix improves. This does not alter the omitted
coefficient rule or turn a boundary check into an unchecked assumption.
