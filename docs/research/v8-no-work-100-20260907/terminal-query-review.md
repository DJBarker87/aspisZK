# Shared terminal query weights: measured all-shape V7 comparison

Continuation of `04e2d26e9b7b169e95fe11d0d62d4225b8c9b795`, 2026-09-09.
The named next experiment succeeds. Sharing the four terminal query-weight
evaluations, specialising their fixed shape and fusing the carried image
coefficient reduces complete CU. A final code-layout change clears an
inherited compiler frame diagnostic at a measured cost of 42–43 CU.

## Selected result

| Complete transaction | Previous V8 | Selected V8 | Same-pool V7 control | Selected V8 − V7 |
|---|---:|---:|---:|---:|
| Transfer, current page | 1,025,815 | **1,015,793** | 1,040,823 | **−25,030** |
| Transfer, rollover | 1,038,559 | **1,028,546** | 1,034,401 | **−5,855** |
| Withdrawal, current page | 1,044,027 | **1,034,027** | 1,036,365 | **−2,338** |
| Withdrawal, rollover | 1,057,043 | **1,047,041** | 1,048,884 | **−1,843** |

These are maxima over three fixed maximum-body proofs per shape under the
pinned runtime/build/account conventions. **The measured four-shape comparison
now favours V8.** It is not a universal no-regression theorem for all accepted
inputs, all schedules or future runtimes. The worst measured complete total is
152,959 CU below the actual 1.2M cap. Body remains **40,282 bytes**.

The selected build passes 24 maximum-body cases, 24 ordinary-body cases and two
post-real-verifier failing-Token-CPI rollback cases. Together with the three
intermediate 24-case matrices, this turn executes **122 complete cases**.
The auditor matches each V8 proof by SHA, and checks context/authoritative-path,
atomicity/account effects, return-data hash/length, outcome and error against
the preceding retained build. These are Pool + research verifier + Registry +
successful Token 3.5 transactions, not a verifier-only subtotal. Rollback uses
the explicit failing Token double and confirms the real verifier CPI happened.

The Pool, Registry, Token, V7-control and driver artifacts are inherited
unchanged. TxV1 explicitly declares 1,200,000 CU; the driver positional argument
remains 1400000 to avoid its old diagnostic-limit override. The selected new
1,027,608-byte verifier ELF is:

```text
3d07a23833bac533f791b7ce2d619f4cd40aff6e1b5314c3b43be596b38c15a3
```

[Exact ledger](terminal-query-results.json),
[auditor](experiments/audit_terminal_query.py), and
[public evidence](evidence/terminal-query/) pin every intermediate separately.

## Measured progression

| Implementation | Worst observed complete CU | Change versus previous step on identical proofs |
|---|---:|---:|
| Previous shared-gamma | 1,057,043 | — |
| Existing `weight_prefix::<4>` | 1,049,464 | about −7,600 CU |
| Fixed four-entry LineM31Batch specialization | 1,047,204 | −2,255 to −2,265 CU |
| Merge image coefficient and four-product terminal dot | 1,046,999 | −180 to −206 CU |
| Separate semantic terminal call (`inline(never)`) | **1,047,041** | +42 withdrawal / +43 transfer |

The last variant is selected despite the small cost because it clears the
compiler's frame-layout diagnostic. Intermediate variants are benchmark
controls, not selected alternatives with equivalent stack evidence.

## Exact arithmetic, not removal of checks

After the three query-side dual folds, one LineM31Batch remains at log length 2.
The old terminal calls `weight_at` four times. At a single query its four
values are

```text
[s, s*x, s*pi(x), (s*x)*pi(x)],       pi(x)=2*x*x−1.
```

The generic prefix path already shares these values, but constructs temporary
factor vectors and obtains entry 3 from entry 2. The fixed path checks `N==4`,
`log_len==2`, exactly one component and its LineM31Batch variant. It then
computes the four entries in one traversal, accumulating four sums and applying
the **same deferred halvings after aggregation**. All other shapes retain the
original fallback. No component is omitted on an honest-zero assumption.

At source level, the reference performs 88 index walks and 88 mixed multiplications.
The fixed path performs 22 walks and 66 mixed multiplications. Source `double_x`
calls fall from 176 to 44 in the generic prefix and 22 in the specialization.
Some old last-factor work can be removed by the compiler already; these counts
are not CU forecasts. The 24 QM31 half operations, all 22 query scales, point
coordinates and three dual folds are retained. Scalar injection still uses
the original shifted rho powers and original dot, not the rejected injection
variants from the last turn.

The terminal's separate `image * final[3]` product is then combined by placing
`image` in weight 3 before calling the existing four-product helper. This is
distributivity inside the already-carried relation. The image check has not
become a final256-only membership check or been dropped. The four-product
helper uses the selected partial-channel kernel and its existing u64 bound.

No parser, canonicality, commitment, query index, Merkle input, root, semantic
constraint, ordinary shifted row, degree-q query batch, scalar recurrence,
challenge request, transcript absorption, nonce or public message changes.
Malformed-input rejection order before the terminal is untouched. The final
field equality is the same predicate for arbitrary inputs, not just valid
payments. Source/SBF refinement remains distinguished below.

## New Lean endpoint and its boundary

[`TerminalQuery.lean`](experiments/TerminalQuery.lean) consumes pinned cached
QueryInjection/QueryAffine/SharedGammaDots/SemanticCarry/AffinePrimal/QmCrossRange.

| Interface | Kernel-checked result |
|---|---|
| Literal low-bit traversal | All four `indexed 2 i s x` values equal the explicit shared vector |
| Generic prefix order | Constructing entry 3 from entry 2 equals constructing it from entry 1 |
| Whole batch | One vector accumulation equals four independent indexed folds, for an arbitrary list and accumulator |
| Deferred normalization | Equality persists after any common number of half maps; the selected count is six |
| Dual factor | The line factor equals the actual `[1,alpha³,alpha²,alpha]` dual contraction before normalization |
| Image integration | Sparse coefficient 3 fusion preserves the whole terminal scalar and its equality-to-claim predicate |
| Four-product helper | Canonical channel decomposition/raw group/partial reconstruction equals the explicit tower-product fold; every four-product prefix fits u64 |

The proofs do not assume an image-valid witness, zero query residuals or
successful extraction. They are source-shaped field/integer identities,
**not a translated Rust/LLVM/SBF theorem**. The half-map lemmas state the
algebraic interface; the source applies the identical existing half operation
to identical canonical sums. No new unchecked range kernel is introduced.
The final helper's cast/reconstruction and integer bounds reuse proved leaves.

Fifteen final axiom reports use only standard propext/Classical.choice/Quot.sound;
there is no retained `sorry` or new axiom. v1 failed because `prefix` is a Lean
keyword; v2 proves the initial leaf, v3 generalises deferred counts, v4 adds the
literal raw-product endpoint. Only v4 is the final result. Source and imported
olean provenance are pinned by the runner. No package/dependency replay ran.

The corrected optimized Rust gate actually executes 1,024 arbitrary query
batches against all four independent indexed evaluations, 45 shape/fallback
cases with 0–8 deferred halvings, and 1,024 arbitrary image-terminal scalar
comparisons plus three canonical extremes. The shapes include empty, dense,
tensor and multiple-component paths and a three-entry prefix fallback. These
are differential tests, not exhaustive adversarial games or security-bit
measurements.

## Two evidence defects found and corrected

First, the initial host runner omitted the enclosing payment/performance
module, so Cargo reported **zero matching tests**. Those three22-second logs
are failed test-discovery preflights, not unit-test passes. Complete SBF
transactions did execute independently. Enabling the correct modules exposed
a missing test-only `HOST_HASH` alias required by imported prover test modules.
The second selected host attempt exits 101; its log is preserved. A small
`cfg(all(test,v8_payment_extraction))` alias supplies the existing SHA callback;
it is archived as a **host-test-only patch**, absent from the SBF build source.
The corrected runner requires both one passed test and the named result marker.
The final 5.50-second gate genuinely runs the tests. No unchanged SBF rebuild
was needed for that test-only fix.

Second, build logs—including the previous retained build—contain twelve
uppercase `Error:` call-frame diagnostics in the semantic function. The
older resource helper only rejected lowercase `error:` or oversized direct
offset diagnostics. A short r10-offset scan does **not** discharge call scratch
overlap. Rather than assume the messages harmless, this turn adds only
`inline(never)` at the existing `payment_terminal` call boundary. The selected
build emits **none** of these diagnostics, retains the full function body,
and passes all 50 selected complete cases. Its runner now rejects both error
spellings and frame-overflow messages. Final direct offsets remain ≤4,096.
This improves the engineering evidence; it still is not a whole-machine stack
proof or a retrospectively established safety theorem for the older ELFs.

## Resources, reproduction and source isolation

| Executed gate | Exit | Wall | Peak RSS | Swaps |
|---|---:|---:|---:|---:|
| Final Lean leaf | 0 | 5.03s | 2,894,036,992bytes | 0 |
| Corrected selected Rust test | 0 | 5.50s | 307,652KiB | 0 |
| Prefix /fixed /fused SBF builds | 0 | 34.56 /34.67 /34.73s | 594,476 /594,624 /594,576KiB | 0 |
| Selected separated-call SBF build | 0 | 34.70s | 594,164KiB | 0 |

The three intermediate builds retain the diagnosed frame messages and are not
clean stack gates. The failed host compile took 21.31 s / 524,556 KiB, exit 101,
zero swaps. Per-case SVM timings/RSS are in the public logs. No full-prover,
peak allocator, browser/phone or new proving-latency measurement is claimed.

NUC task COPY, Rust 1.94.1, SBF tools 1.54/Rust 1.89-dev, LiteSVM 0.16.0/runtime 4.2.1,
opt3/fatLTO/codegen1 and overflow checks remain pinned. Builds use jobs 2,
MemoryHigh 5G/Max 7G; SVM scopes use High 3G/Max 4G; all SwapMax 0. Lean 4.32.0 uses
Mathlib 81a5d257 and `-M7000` with checked cached research dependencies.
Source/ordinary main changes by the concurrent worker were preserved.

The fixed core specialization is an isolated research patch, not a committed
production source edit: `experiments/terminal-query-sumcheck.patch`. Apply it
only in the authorised task COPY with the inherited complete integration and
field overlays. The two research callback edits and flags are source-pinned;
ordinary production/default builds do not activate them. No witness/proof
binary/ELF or real secret is committed.

```sh
# In the research worktree:
python3 docs/research/v8-no-work-100-20260907/experiments/audit_terminal_query.py --check-recorded
bash docs/research/v8-no-work-100-20260907/experiments/run_terminal_query_lean.sh /tmp/NEW-terminal-query-lean.log

# In the pinned NUC task COPY, with the research sumcheck patch installed:
ex=docs/research/v8-no-work-100-20260907/experiments
bash "$ex/run_complete_build_nuc.sh" terminal-stack NEW-build.log
ASPIS_POOL_ZERO_FAST=1 ASPIS_COMPLETE_MAX_FIXTURES=1 \
ASPIS_COMPLETE_TX_LIMIT=1200000 ASPIS_TOKEN_CONTROL=legacy35 \
ASPIS_TOKEN_ELF_DIR=/home/dombarker/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/litesvm-0.16.0/src/programs/elf \
bash "$ex/run_complete_matrix_nuc.sh" terminal-stack NEW-max
# Repeat without ASPIS_COMPLETE_MAX_FIXTURES for ordinary proofs.
# Rollback must NOT inherit successful-Token override variables:
ASPIS_V8_TERMINAL_STACK=1 bash "$ex/run_pool_zero_cases_nuc.sh" rollback NEW-rollback
```

For the unit gate, install the separate host-test patch, run
`ASPIS_TERMINAL_STACK=1 bash "$ex/run_terminal_query_nuc.sh" NEW-test.log`, then
restore only that test patch. Build and test source guards deliberately expect
different root hashes. Historical prefix/fixed controls require their archived
structured/kernel sources; guards fail closed rather than silently retest the
new winner. The scripts refuse existing output targets.

## Remaining decision

This closes a useful **measured engineering milestone**: all four maximum-body
shape maxima beat their matched V7 controls at the accepted body size. It does
not establish that every accepted schedule/context has the same headroom.
The narrowest measured V7 margin is 1,843 CU, so universal parity must not be
inferred from these fixtures.

The next decisive experiment is an actual-source CU upper-bound audit of the
selected traversal, separating fixed-size arithmetic/authentication from
challenge rejection/retry work. Use the emitted code and actual sampler caps,
not average field-operation counts. This should identify whether further
shared challenge preparation is needed for robust parity, rather than just
another average-case reduction. Existing global recovery, FS-resource and
full-view privacy obligations stay unchanged; no positive grinding credit,
invented compiler-error probability or global security subtotal is introduced.

Body: `697*16+52+24+22*621+2*296*26 = 40,282`; new proof/transcript bytes: zero.
The selected arithmetic reuse spends neither query count nor security margin.
