# Complete transactions and range-proved QM31 rewrites

Date: 2026-09-09. Base research revision:
`8fba5920852911f5666a0982ecc5dd9f0048b18b`.
Continuation of [range performance](range-performance-review.md), not a new
security design or production activation. All repository changes are confined
to this research directory; integration/field patches run only in the task-owned
NUC source copy. Concurrent main changes were preserved.

## Result

The repaired V8 now runs through **actual authenticated ASQ8 → ASF8 → V8 →
ASR8 → atomic Pool settlement**, for genuine transfers and withdrawals, on
both current and rollover history pages. These are complete local TxV1
transactions, not an isolated verifier plus an estimated settlement cost.

Three range-justified arithmetic changes save about **105k CU** relative to
the initial typed complete verifier. The latest build has these measurements:

| Complete shape | Ordinary proofs: maximum of three | 40,282-byte proofs: maximum of three | Rebuilt selected V7 control |
|---|---:|---:|---:|
| Transfer, current page | 1,163,007 | **1,170,650** | 1,040,836 |
| Transfer, rollover | 1,237,239 | **1,244,066** | 1,095,293 |
| Withdrawal, current page | 1,176,426 | **1,182,365** | 1,030,338 |
| Withdrawal, rollover | 1,250,443 | **1,256,466** | 1,103,736 |

All six maximum-body current-page cases also pass with an actual **1,200,000
TransactionConfig limit**. Rollover still misses the all-shapes goal by up to
**56,466 CU**. No-regression against selected V7 is **not met**. These are
observed fixture maxima, not universal bounds over accepted statements,
PDA bumps, query schedules or malformed-input paths.

The new host build produces byte-identical transfer proofs in
**3.20338 /3.15368 /3.15396 seconds**, mean **3.17034**, plus **1.42998 seconds**
shared setup. Peak process RSS is **202,456 KiB /197.71 MiB**, zero swaps.
This is NUC host proving, not mobile/browser latency or extraction time.

[Exact results and audited comparison](complete-performance-results.json),
[commands/pins/scope](complete-performance-evidence.json),
[evidence directory](evidence/complete/),
[reconciliation script](experiments/audit_complete_evidence.py).

## What is genuinely connected

The complete harness independently constructs the synthetic Pool account
context and exports canonical ASF8, verifier identity and proof-account identity
**before loading a proof**. The actual compiler/prover receives that context,
checks its witness anchor/asset/sequence, and asserts that its compiled append
transition equals the authoritative statement. The C1/C2 masks, H/G/D helpers,
literal selected semantic producer and compact repaired relation remain live.
Withdrawal uses its actual selected terminal, not a transfer surrogate.

The proof is then supplied to the original combined TxV1 harness. It constructs
Registry V2 through actual instructions against the loaded Program/ProgramData
ELFs; validates release, account ownership, readonly privileges, PDAs, checkpoint,
lane and sealed proof; reconstructs ASF8; verifies the proof; checks the literal
792-byte ASR8; settles the nullifier, lane and history; and performs withdrawal
token CPI. Returned states are compared byte-for-byte with expected transitions.
No successful case uses the result-double verifier.

The research callback takes typed statement/transition objects **after those
canonical/account checks**. This removes a public encode/decode round trip,
not a validation of untrusted input. Profile/release and attempt binding have
distinct research framing in [complete_binding.rs](experiments/complete_binding.rs).
The attempt binds the ASF8 digest, profile, release, verifier and proof account.
This replaces the older synthetic performance binding; it is a research
transcript integration, not byte identity with that older proof.
All subsequent arithmetic comparisons use the same complete-bound proof bytes.

Integration is retained as [complete-integration.patch](experiments/complete-integration.patch)
and [complete-matched-driver.patch](experiments/complete-matched-driver.patch).
No repository production dispatcher, acceptance default or deployment manifest
was edited. The research callback is not a completed source/FS/knowledge theorem.

## Three retained arithmetic changes

1. **Direct QM31 cross component.** Preserve the original c0 tower expression;
   compute the two c1 limbs as four raw products each. Positive padding by 2p²
   makes the signed channel nonnegative. Every u64 prefix is bounded. This
   deliberately uses more base products than Karatsuba but fewer canonical
   additions/subtractions, and saves about **52.3k complete CU**.
2. **Partially reduced c0 reconstruction.** Use
   `fold(x)=(x & p)+(x>>31)`, which is congruent to x modulo p but need not
   be canonical. Group positive products before folding; use 8p padding for
   signed output channels; canonicalize the two output limbs only at the end.
   Generic and prepared multiplication share the same actual input coordinates.
   This saves about **26.5k additional complete CU**.
3. **Seven-chunk gamma accumulation.** Keep each four-product chunk partially
   reduced instead of canonicalizing it. Each chunk is below 5p; all seven and
   every nonnegative prefix total less than 35p < 2³⁷. Only the final four output
   limbs are canonicalized. This saves **26,488 CU on every tested transaction**,
   with identical proof bytes, queries, roots and checks.

The first two patches are [qm-hybrid](experiments/qm-hybrid.patch) and
[qm-lazy-c0](experiments/qm-lazy-c0.patch). The third is the inactive-by-default
`v8_gamma_partial` path in [query_arithmetic.rs](experiments/query_arithmetic.rs).
The original field source remains unchanged in Git. The existing six range
patches remain prerequisites; the measured-regressing branchless cfg stays off.
Global overflow checks remain **enabled** in the research verifier.

For attribution with the same checked Pool wrapper, seed-1 transfer falls from
1,268,257 to 1,215,941 CU with the first rewrite. With the final selected Pool
wrapper, hybrid → lazy → partial is 1,214,285 → 1,187,801 → 1,161,313.
The intervening 1,656-CU difference is a Pool build-policy change, not an
arithmetic saving. Full tables retain each artifact hash.

### Formal and source boundaries

[QmCrossRange.lean](experiments/QmCrossRange.lean) proves product bounds,
signed-prefix safety, modular padding identities, both cross-component ring
identities, partial-fold congruence/range, c0 algebra, list-sum congruence and
the seven-chunk bound. These are symbolic integer/ring facts.
The existing M31 mask/shift/reducer bridge and earlier range facts are reused.

| Obligation | Evidence |
|---|---|
| Algebraic equality of new field expressions | Kernel-checked ring identities |
| Raw accumulator / signed-prefix / partial-sum bounds | Kernel-checked symbolic natural/integer facts |
| Actual generic/prepared arithmetic | Optimized Rust tests against independent u128 modular formulas |
| Packed gamma and rejection of every noncanonical limb position | Source-shaped differential controls, including all-maximal limbs |
| Complete proof bytes unchanged under arithmetic rewrite | Three regenerated proofs compare byte-identical |
| Actual complete acceptance and tested atomic rollback | SBF/LiteSVM execution |
| Canonical-input provenance / decoder invariants | Existing source audit; not a universal translated invariant proof |
| Whole patched Rust acceptance equivalence | Not completed; no placeholder premise is called a source refinement |

Canonical parsing, nonzero-denominator checks, all row/image weights, shifted
query batching, relation boundaries and authentication remain. No honestly-zero
residual has been deleted. No new proof value, mask, nonce or round is introduced.

Final focused Lean command:

```sh
cd /Users/dominic/ZK/AspisFormal
/usr/bin/time -l lake env lean -M7000 /ABS/experiments/QmCrossRange.lean
```

Lean 4.32.0, cached mathlib
`81a5d257c8e410db227a6665ed08f64fea08e997`.
Exit 0, **8.28s /2,850,930,688-byte RSS /zero swaps**.
[Final log/axiom audit](experiments/complete-partial-lean.log) records only
standard propext/Classical.choice/Quot.sound, with no sorry or new axioms.
Earlier c0-only success is separately retained. Local preflight naming/simp
recursion errors were fixed symbolically, not with larger reduction limits.
No package-wide Lean replay or Aeneas rebuild was run.

The optimized field control runs 32 original tests and two independent
boundary/differential tests, including 256 zero/maximal eight-limb patterns and
8,192 pseudorandom products, generic and prepared. Final field run:
exit0, 0.01s, 2,992-KiB RSS, zero swaps. This tests arithmetic, not a 2⁻¹⁰⁰
probability. [Field log](experiments/complete-qm-lazy-rust.log).
The updated complete host additionally runs the actual packed/structured/dense
controls, then produces and verifies the genuine transfer proofs.

## Matched comparison and stress scope

The final V7/V8 comparison uses the same NUC, SBF v1.54 tools/compiler,
LiteSVM 0.16.0 / Solana runtime 4.2.1, actual TxV1 accounting, account shapes,
and identical selected Pool/Registry ELFs. V7 uses four existing canonical
strict-work proofs, one per shape, and executes its original work checks.
Those checks contribute no V8 security credit.

Withdrawal CPI uses the inherited harness's LiteSVM legacy SPL Token builtin,
identically for V7 and V8. This is not a timing measurement of the production
SPL Token SBF binary. The local full-transaction measurements must not be
promoted to production-CU or deployed-feature availability claims.

Build policies are **not identical**: V7 is rebuilt from its original workspace
release profile and lock; V8 uses the isolated fat-LTO/codegen1,
overflow-checks=true profile and lock. A separate overflow-checked standalone
V7 wrapper exhausted 1.4M and is rejected as a misleading selected baseline.
The direct-source selected control above is faster, so historical 1.14–1.20M
figures cannot establish parity. Matching release policies more tightly is
still a requirement for any eventual no-regression certificate.

For the maximum-body controls, commitments and prior responses are fixed;
the existing last nonce is scanned for a 296-node frontier in each tree, with
a predeclared one-million-attempt cap per seed. All twelve cases found a schedule.
This deliberately makes authentication expensive. It is not the ordinary
proving algorithm, an enforced security sampler or positive work credit.
Every observed attempt count/time is in the results; three observations per
shape do not establish p95/p99 or universal latency. The real FS ledger must
retain adversarial nonce/retry selection.

The final ordinary and maximum-body matrices each contain 12 successes,
proof-corruption and wrong-release rejection on all four shapes, and current-page
stale-lane/replay controls. Replays preserve already-settled state; other failures
preserve all accounts. Both withdrawal token-CPI failures execute the real
cryptographic verifier and roll back the complete transaction. Rollover replay
and stale-lane fixtures are explicitly unsupported by the inherited harness;
initial attempts stopped at that guard and were not reported as passing tests.
This is not an exhaustive malformed-proof, sampler-exhaustion or CU-tail audit.

An initial 1.2M test incorrectly selected the driver's diagnostic runtime-budget
override, which also reset heap policy and failed at entry. The corrected test
keeps the ordinary runtime and puts 1.2M in TransactionConfig, preserving the
requested 256-KiB heap. Both logs are retained; the failed setup is not counted
as a cryptographic rejection or a pass.

## Wire, memory and remaining cost

```text
697*16 + 52 + 24 + 22*621 + 2*296*26 = 40,282 proof-body bytes
```

Separate overhead: 40-byte ASPU header, 688-byte candidate afterstate,
320-byte ASQ8 instruction, reconstructed 1,880-byte ASF8, 792-byte ASR8.
Actual transaction serialization is 845/878 bytes for transfer and 1,010/1,043
for withdrawal, current/rollover respectively. Account-resident proof bytes
are not ordinary transaction payload bytes. Upload/create/seal/rent costs are
not included in the complete payment-operation CU.

Latest quiet ELF:
`f55df9b5881b5ed98c6fcc93ea27bde96ae8d80597b1b9b2c5365e5b09ca7e3a`.
The unstripped emitted artifact has maximum direct r10 offset 4,096 across
177 labelled functions; no build stack warning.
[Stack audit](experiments/complete-stack.json) is not a proof about every
derived machine pointer. The stripped file only preserves a few symbol names;
its label count was not used as a function census.

Latest SBF build: **34.16s /589,072-KiB RSS /exit0 /zero swaps**.
NUC Core Ultra 7 155H, 22 logical CPUs, approximately 62 GiB RAM.
Builds use systemd scopes: MemoryHigh5G, MemoryMax7G, MemorySwapMax0; proof/SVM
jobs use 3G/4G/0. Host build: 26.50s /519,828 KiB. No remote RPC, paid job,
deployment or production key material was used. Synthetic proof/context artifacts
are retained; no secret-bearing witness table is exported.

The profiled **lazy** complete build locates 73,739 CU of the transfer rollover
premium before verifier CPI. The cryptographic verifier itself differs by only
1,921 CU between those two fixtures, principally query authentication.
This rules out attributing that premium to a more expensive semantic terminal.
The exact pre-CPI cause still needs substage profiling; do not call the whole
interval Merkle cost, root reconstruction or removable validation.

Within the lazy verifier, the measured semantic terminal is about 272k,
packed gamma about 189k (the new rewrite saves 26,488 from the complete total),
internal query authentication about 137–140k, grouped/point terminal
about 41k/34k, and final coefficient folds about 44k.
Profile calls inflate total CU; only quiet whole transactions set the headline.

## Reproduce / next decision

Use an existing task-owned NUC source copy of the pinned branch; preserve caches.
The preparation script refuses a Git worktree and pins original/final source
hashes. It applies the six earlier range patches, two new field patches,
complete integration and driver patches. It does not fetch, reset or deploy.
Standalone Cargo locks are retained.

```sh
bash experiments/prepare_complete_nuc.sh
bash experiments/run_complete_build_nuc.sh partial NEW_SBF_LOG
bash experiments/run_complete_build_nuc.sh partial-host NEW_HOST_LOG
bash experiments/run_complete_build_nuc.sh driver NEW_DRIVER_LOG
# Build selected-v7 / selected-pool / selected-registry once with cached tools.
ASPIS_SELECTED_POOL=1 bash experiments/run_complete_matrix_nuc.sh partial NEW_MATRIX
ASPIS_SELECTED_POOL=1 ASPIS_COMPLETE_MAX_FIXTURES=1 \
  bash experiments/run_complete_matrix_nuc.sh partial NEW_MAX_MATRIX
bash experiments/run_complete_special_nuc.sh cap1200-partial-max NEW_CAP_MATRIX
python3 experiments/audit_complete_evidence.py
```

Actual absolute commands, exits, RSS, wall times and swaps are retained in
`evidence/complete/*.log` and each experiment directory. Matrix scripts name
the existing deterministic fixture directories; regenerate them with
`run_complete_fixture_nuc.sh` and its documented environment switches.
The result-double ELF is only a required harness input/negative-control option,
never the accepted verifier in the reported cases.

**Retain the three arithmetic rewrites. Continue q22 optimisation.** Both
current-page transaction shapes now have maximum-body evidence under 1.2M.
Rollover and selected-V7 parity are still unmet, so the optimisation goal remains
active. Global accepted-extraction error, full-view ZK, resource-bounded FS and
translated source correspondence remain symbolic/open; these measurements add
no security bits.

The single next experiment is a **fine profile of the complete Pool pre-CPI
path on the same current/rollover inputs**, separating history-page validation,
new-page handling and registry/PDA work, followed by an exact-equivalence
candidate for the dominant stage. A second bounded arithmetic candidate is
directly reconstructing the nine partially reduced Karatsuba channels into four
output limbs. Neither saving is booked until whole-transaction measurement.
No claim is made that all optimisations are exhausted.
