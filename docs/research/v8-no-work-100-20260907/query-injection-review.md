# Query injection and helper hoisting: exact rewrites, no retained CU saving

Continuation of `a1925696fede0c3b3ca3745ebe0ca4bd8a5a588f`, 2026-09-09.
The named helper-hoist experiment was executed, followed by three different
lowerings of the shifted q22 scalar injection. **All four are rejected as
performance changes.** The selected research verifier source is restored
byte-for-byte. Production/main and the protocol are unchanged.

## Complete-transaction decision

| Control | Same-proof CU change | Worst complete CU | ELF bytes |
|---|---:|---:|---:|
| Retained shared-gamma | — | **1,057,043** | 1,007,416 |
| Hoist immutable H/G/D helper array outside four-slot loop | 0 | 1,057,043 | 1,007,416 |
| Prepared rho array + existing generic long dot | +2,874 to +2,917 | 1,059,940 | 1,022,768 |
| Prepared rho array + fixed six-group partial dot | +377 to +416 | 1,057,442 | 1,013,632 |
| Original rho Vec + fixed six-group partial dot | +584 to +623 | 1,057,649 | 1,013,000 |

Each comparison uses the same twelve 40,282-byte proofs: three per transfer/
withdrawal × current-page/rollover shape. Each control also runs the applicable
malformed-proof, wrong-release and replay cases: **96 new complete cases** in
total. The auditor checks identical proof/fixture identities, authoritative
path, account/atomicity fields, return-data hash/length, outcome and error.
These are actual Pool + research verifier + Registry + successful Token3.5
transactions at an **actual TxV1 limit of 1,200,000 CU**, not isolated verifier
measurements or an enlarged diagnostic budget. The pinned driver's positional
argument remains1400000; the explicit limit variable supplies the actual cap.

The fixed dot improves the generic lowering by about2,500CU. Keeping the old
power Vec then costs exactly207CU on these twelve proofs compared with the
array version. Neither wins. This does not isolate an instruction-level cause:
all three change code generation and ELF size as well as source arithmetic.
Do not infer that fewer field reductions must lower metered CU.

Helper hoisting leaves all measured CU unchanged. A separate read-only ELF
audit finds **different allocated text/data**, despite equal ELF/text sizes;
it is not claimed to be a compiler no-op. Stripped final symbols prevent a
precise helper-function attribution. Its unchanged complete cost is enough
to reject it as a measured saving here.

Since every control either ties or loses, no control is expanded to ordinary
proofs or post-verifier failing-Token-CPI rollback. The retained build's prior
24maximum +24ordinary +2rollback cases remain its evidence; they were not
rerun unchanged. The retained maxima by shape remain1,025,815 /1,038,559 /
1,044,027 /1,057,043. Same-pool V7 deltas remain−15,008 /+4,158 /+7,662 /+8,159.
There is no universal CU certificate or all-shape V7 parity claim.

[Exact ledger](query-injection-results.json),
[auditor](experiments/audit_query_injection.py),
[helper evidence](evidence/helper-hoist/) and
[injection evidence](evidence/query-injection/) pin the actual binaries and
source overlays. The retained ELF is still
`8540f1abb5ca393500058323aec1b9212375159ca1de87e8fbfeede5319bd958`.

## What was changed and proved

The reference callback emits `[rho,rho²,…,rho²²]`, installs the corresponding
line covectors, computes their scalar dot and adds it to the prior claim. It
performs one unused final power update. The first new version emits the same
22values using a seeded array and21updates, with a prepared rho multiplier.
The actual existing `qm31_dot` takes its long path at22values: six blocks of
lengths4,4,4,4,4,2 inside one outer window. It performs63canonical channel
reductions before the output reconstruction.

The fixed version replaces that general reduction schedule with the literal
six-block partial-channel construction. It uses198base products,63partial
folds and4final output reductions; decomposition additions, reconstruction,
data movement, shape checks and power preparation remain real costs. The
third version changes only this dot while preserving the old Vec producer.
These counts are not CU estimates.

[`QueryInjection.lean`](experiments/QueryInjection.lean) proves:

| Interface | Proven fact |
|---|---|
| Power producer | Old emit-then-update traversal and seeded producer return identical ordered22powers; only the unused state differs |
| Scalar injection | The emitted-list dot equals `rho * Horner(values)` |
| Prior discrepancy | `prior + rho*received - rho*expected = prior - rho*(expected-received)`; no unshifted constant cancellation is introduced |
| Generic dot | Canonical per-channel reductions and grouped accumulation preserve the literal tower-product sum |
| Fixed grouping | The six blocks cover indices0..21 exactly, including the final pair |
| Fixed arithmetic | Literal raw/partial-channel accumulation and reconstruction equal the flattened tower-product sum |
| Machine ranges | Every four-product raw prefix fits u64; canonical and partial six-group accumulator prefixes fit u64 |
| Shape rejection | The exact zero-log/empty/length-mismatch guard is equivalent to the stated admissible shape |

The partial reconstruction body is checked byte-for-byte against the earlier
proved `SemanticCarry` body. Existing cast/tower and reduction lemmas are
reused from pinned QueryAffine/SharedGammaDots dependencies, not replaced by
an assumed equality. The new exact integer maxima include
`4*(p-1)^2 = 18,446,744,039,349,813,264 < 2^64` and
`6*(5*p+3) = 64,424,509,428 < 2^64`.

This is a kernel-checked algebra/integer interface, **not a translated
Rust/LLVM/SBF theorem**. The packed parser and query code are unchanged by
the injection controls. The callback dispatches only exact q22 arrays to the
new kernel; other lengths retain the reference fallback. Line-batch shape
rejection still happens before scalar mutation. No image, ordinary-row,
query-batch, semantic, authentication or terminal check is removed; no
transcript boundary, challenge, nonce or proof value moves.

Optimized source-shaped tests cover512arbitrary rho/value profiles, zero/one/
maximal limbs,32full line-weight tails under three actual arity-four folds,
and75log/length shape combinations. Fixed variants add2,048arbitrary dot
comparisons against naive multiplication, independent of a power sequence.
The helper control reuses the changed path's packed gamma tests, including
152noncanonical positions and two short inputs. These tests are not
exhaustive malicious strategies or experimental measurements of tiny errors.

## Resources and reproduction

| Job | Exit | Wall | Peak RSS | Swaps |
|---|---:|---:|---:|---:|
| Final QueryInjection Lean leaf | 0 | 2.18s | 2,902,507,520bytes | 0 |
| Helper hoist Rust / SBF | 0 /0 | 22.90s /34.20s | 514,508 /592,960KiB | 0 |
| Generic injection Rust / SBF | 0 /0 | 23.20s /34.48s | 517,856 /593,188KiB | 0 |
| Fixed array Rust / SBF | 0 /0 | 23.23s /34.40s | 515,416 /593,976KiB | 0 |
| Retained powers Rust / SBF | 0 /0 | 23.26s /34.54s | 516,136 /593,380KiB | 0 |

The21final axiom reports contain only standard axioms; two finite index
identities use no axioms. v1 failed on an over-unfolded list step; v2 proved
the generic endpoint; v3 adds fixed partial accumulation. Failed output is
retained but excluded from the result. No retained theorem has `sorry` or a
new axiom. Source/olean hashes and cached Mathlib revision are checked by
`run_query_injection_lean.sh`; unchanged dependencies were not replayed.
Lean4.32.0, Mathlib81a5d257, local `-M7000`; no package/certificate replay.

The authorised NUC task COPY and selected field overlay are reused. Host
Rust1.94.1; SBF tools1.54/Rust1.89-dev; LiteSVM0.16.0/runtime4.2.1;
SBF opt3/fatLTO/codegen1 with overflow checks enabled. Builds run jobs2,
MemoryHigh5G/MemoryMax7G; SVM scopes High3G/Max4G; all MemorySwapMax0.
Compilation dominates these focused Rust gates. Final static r10 offsets are
≤4,096 for all four ELFs. This direct-offset scan is limited, not a whole
machine-stack proof. All per-case resource logs are preserved.

From the research worktree:

```sh
python3 docs/research/v8-no-work-100-20260907/experiments/audit_query_injection.py --check-recorded
bash docs/research/v8-no-work-100-20260907/experiments/run_query_injection_lean.sh /tmp/NEW-query-injection-lean.log
```

To reproduce a rejected SBF control, use an isolated task COPY at the recorded
revision with the inherited complete integration and selected field overlays.
Apply `experiments/query-injection-callback.patch` there. Install the exact
kernel archive as `query_injection.rs`: generic, fixed_array or the retained-
powers file. Do not apply these rejected patches to the selected worktree.
Each source guard fails closed on a different revision/kernel. Example for
retained powers, from that COPY:

```sh
ex=docs/research/v8-no-work-100-20260907/experiments
ASPIS_QUERY_INJECTION_RETAINED_POWERS=1 bash "$ex/run_query_injection_nuc.sh" NEW-test.log
bash "$ex/run_complete_build_nuc.sh" query-injection-retained-powers NEW-build.log
ASPIS_POOL_ZERO_FAST=1 ASPIS_COMPLETE_MAX_FIXTURES=1 \
ASPIS_COMPLETE_TX_LIMIT=1200000 ASPIS_TOKEN_CONTROL=legacy35 \
ASPIS_TOKEN_ELF_DIR=/home/dombarker/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/litesvm-0.16.0/src/programs/elf \
bash "$ex/run_complete_matrix_nuc.sh" query-injection-retained-powers NEW-matrix
```

Generic uses no selector; fixed array uses `ASPIS_QUERY_INJECTION_FIXED=1` and
mode`query-injection-fixed`. Helper hoist instead applies only its query patch
to the baseline, then uses its dedicated test/build/matrix mode. The scripts
refuse existing output targets. Only public synthetic JSON/logs, not witnesses,
proof binaries or ELFs, are committed. Exact integer ledgers are generated and
checked with Python integers, not round-tripped through binary64 JSON.

## Next bounded target

`structured_weights::relation` still calls `query_weights.weight_at(i)` four
times at log2. Each LineM31Batch evaluation walks all22queries and reconstructs
the same `x, pi(x)` factors. A single traversal can produce
`[s, s*x, s*pi(x), s*x*pi(x)]` per query with shared factors, accumulate all
four entries, then apply the same six deferred halvings. First compare the
existing `weight_prefix::<4>` control, whose generic implementation allocates
factor vectors, against a fixed-size research-only traversal. Do not infer a
saving from the formula or bypass the checked weight constructor.

The decisive experiment is a **same-proof complete SBF comparison of that
four-output terminal traversal**, preceded by a symbolic distributivity/halving
bridge and arbitrary-input differential tests. An optional subsequent fusion
can place the image weight in coefficient3 before the four-product terminal
dot; it must retain the image contribution, not reinterpret it as a separate
late membership test. Rejection of this injection family does not close that
different opportunity.

Body remains `697*16+52+24+22*621+2*296*26 = 40,282`. Extra proof bytes and
grinding credit remain zero. No new prover timing/RSS measurement, global
security/FS/privacy certificate, universal CU bound or release decision is
inferred. The existing unresolved protocol obligations remain unchanged.
