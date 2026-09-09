# Compact semantic coefficient: reduce once per limb

Continuation of `9d783f0f880dfa263f9a39c90da3093adb86ffe0`, 2026-09-09.
This retains the second, independently measured rewrite from this continuation.
Production/main, proof grammar, transcript and all checks are unchanged.

## Complete-transaction result

| Shape | Semantic-carry maximum | New maximum | Same-pool selected V7 excess |
|---|---:|---:|---:|
| Transfer, current page | 1,057,234 | **1,050,628** | 9,805 |
| Transfer, rollover | 1,070,020 | **1,063,414** | 29,013 |
| Withdrawal, current page | 1,075,506 | **1,068,895** | 32,530 |
| Withdrawal, rollover | 1,088,538 | **1,081,936** | 33,052 |

Same-proof savings are **6,572–6,612 CU**, determined by proof identity, not
filesystem iteration order. An initial quick diagnostic paired some seed rows
incorrectly; its 6,194–6,990 range is superseded by this audited range. The
reported worst total was unaffected. Across both retained rewrites, the worst
complete total improves from 1,091,626 to 1,081,936 CU: **9,690 CU saved**.

The actual TxV1 cap is 1,200,000, leaving **118,064 CU worst-observed headroom**.
These are fixture maxima, not a universal bound or no-regression result against
V7. All 24 maximum-body cases, 24 ordinary-body cases and two post-real-verifier
failing-Token-CPI rollback controls pass with unchanged outcomes, proof identity
and protected-account comparisons. The same pinned Pool/Registry/Token3.5 SBF
surround successful execution. Rollback uses the intentionally failing Token
double, after actual V8 verification. Unsupported stale/replay rollover cases
remain uncounted.

The new ELF grows by 1,624 bytes to **1,012,312 bytes**, SHA256:

```text
ee856b7131a7084a9287b04444cbb7b4b84d3a914dd3d4e182182c02229e6736
```

This code-size cost is retained because actual full-transaction CU improves.
[Results](semantic-boundary-results.json) and the
[auditor](experiments/audit_semantic_boundary.py) contain every proof delta,
artifact/source pin, resource measurement and axiom audit.

## Source-shaped equation and canonical-input boundary

The real semantic parser reconstructs 28 coefficients from 27 transmitted
canonical QM31 values. `poly[0]` and `poly[2..28]` are transmitted; the omitted
coefficient is exactly

```text
poly[1] = prior_claim - 2*poly[0] - sum(poly[2..28]).
```

[`semantic_boundary.rs`](experiments/semantic_boundary.rs) implements that
same expression per canonical base limb. It accumulates the 26 tail limbs as
u64 integers, then reduces `claim + 28*p - 2*c0 - tail_sum` once. It does not
remove the reconstruction or assert a boundary from an honest fixture.

Before compiler simplification, each old round has 28 QM31 additions and one
subtraction. The new round has 108 u64 additions, eight subtractions, four
times-two operations and four final M31 reductions, with no heap allocation.
There are ten rounds. These are literal operation inventories, not CU forecasts.

The parser still checks all 697 fixed QM31 values for canonicality. The initial
prior claim is one of those values; subsequent claims are canonical evaluator
outputs. Thus every call receives canonical limbs from the actual unchanged
input path. The tail has statically 26 elements. Its conversion from the
`[K;28]` slice cannot be made shorter by a prover. No unsafe read or unchecked
prover hint is added.

The response bytes, omitted-index convention, absorption order, fresh challenge,
semantic evaluator and terminal check remain unchanged. So do the image gate,
shifted rows, query batch, authentication, context checks and Pool settlement.
Changing when arithmetic reduces does not change any accepted field equation.

## Literal range and field bridge

[`SemanticBoundary.lean`](experiments/SemanticBoundary.lean) proves:

- A canonical list sum is at most its length times `p-1`; every running update
  through 26 elements stays below u64 and wrapping addition is exact.
- For canonical `a,c` and `s≤26*(p-1)`, `a+28*p` is below u64, `2*c` fits,
  both subtractions have nonnegative prefixes, and the final value fits.
- The literal wrapping add/multiply/subtract expressions equal those natural
  integer operations. No field identity is used to excuse integer overflow.
- Casting the result to `ZMod p` gives exactly `a-2*c-s`; casting the accumulated
  list sum equals the sum of individual casts. `missing_from_terms` connects
  the concrete 26-term list to the reconstructed field coefficient, and
  `actual_boundary` proves its original boundary equation.

Numerically: tail≤55,834,574,796; padding=60,129,542,116; positive
prefix≤62,277,025,762, all below 2^64. The eight final axiom audits contain only
standard propext/Classical.choice/Quot.sound. No retained theorem uses `sorry`
or a new axiom, valid-witness premise, decoder premise or honest-residual premise.

These are kernel-checked source-shaped integer/list/field identities, **not a
Rust/LLVM/SBF translation**. Per-limb correspondence, canonical reduction and
compiler lowering retain their explicit source/refinement boundary. No invented
probability is assigned to that boundary.

## Focused evidence

The optimized Rust test compares the actual helper to the old expression and
checks the literal boundary, on arbitrary canonical values, 104 single-limb
basis cells, zero/all-maximal values, minimum and maximum subtraction prefixes.
Complete SBF cases exercise the actual source path, not a witness-side mock.

| Job | Exit | Wall | Peak RSS | Swaps |
|---|---:|---:|---:|---:|
| Final Lean leaf | 0 | 9.65s | 2,901,803,008 bytes | 0 |
| Optimized Rust gate | 0 | 22.47s | 519,172 KiB | 0 |
| Quiet SBF build | 0 | 34.06s | 592,900 KiB | 0 |

The six initial scalar/range facts passed in 11.88s. Extending the source/list
bridge exposed a Lean elaboration issue: an untyped map lambda induced an
unintended List coercion. Two focused attempts failed in 2.27s and 1.72s;
their logs are retained as failures, not proof evidence. Explicit `x:Nat` and
a list induction close the intended eight-fact endpoint. Final evidence is
`semantic-boundary-lean-v4.log`; v2/v3 `sorryAx` entries are failed elaborations,
not retained axioms. No large reduction or package replay was attempted.

The cached AffinePrimal source/olean and Mathlib revision are checked before
the leaf. NUC build scopes High5/Max7GiB/jobs2, SVM High3/Max4GiB, SwapMax0.
HostRust1.94.1, SBF tools1.54/checked Rust1.89-dev,
LiteSVM0.16.0/runtime4.2.1 remain pinned. Direct r10 offsets remain≤4,096,
with no new stack warning; this is not a universal stack theorem. Field overlay
SHA256 remains `bb4b177e4b06da631cef8cc3eaa44b3b08c1bbf3b123b975b116264f447d8fe0`.

## Reproduction and next bounded experiment

```sh
python3 docs/research/v8-no-work-100-20260907/experiments/audit_semantic_boundary.py
bash docs/research/v8-no-work-100-20260907/experiments/run_semantic_boundary_lean.sh NEW_LOG
```

On the authorised NUC task COPY, apply `semantic-boundary-callback.patch` and
`semantic-boundary-verifier.patch` to 9d783f0f, add the kernel and runners.
Run the source guard, `run_semantic_boundary_nuc.sh NEW_LOG`, then
`run_complete_build_nuc.sh semantic-boundary NEW_LOG`. Run the matrix in
`semantic-boundary` mode with maximum and ordinary fixtures, retaining the
same Pool, Token and real 1200000 env cap described in the previous report.
For rollback, omit successful Token overrides, set
`ASPIS_V8_SEMANTIC_BOUNDARY=1` and use the rollback runner. Named earlier modes
require their archived source pins; they must not silently use changed files.

Body remains `697*16+52+24+22*621+2*296*26=40,282`, with zero new proof or
transcript bytes and zero grinding credit. No new prover-time/peak-memory
measurement, global recovery/FS/ZK certificate or V7 parity claim is made.

**Next experiment:** the actual structured preparation uses five separate
29-term `qm31_dot` calls sharing one gamma-power vector: three point rows and
two sequentially committed OOD rows. The pinned implementation decomposes each
gamma weight repeatedly and retains the generic >16-element reduction path.
Test a fixed29 shared-preparation kernel with independent output accumulators
and bounded four-product chunks, without moving either OOD absorption or any
challenge. Prove the five dots equal their references and charge all partial
reductions. Keep it only if complete same-proof SBF measurements improve; a
larger prepared buffer or loop layout may lose CU despite fewer field operations.
This targets the ordinary/OOD calculations, not the previously rejected gamma-one
branch guards in the authenticated query loop.
