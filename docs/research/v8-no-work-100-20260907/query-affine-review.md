# Query-affine fusion: proved equivalent, rejected on complete CU

Continuation of `c3552659714b984fd02b376c2b4e22bebd159c00`, 2026-09-09.
The preceding turn made a measured improvement. This turn executes its named
next experiment, then two bounded alternative lowerings. **None beats the
selected implementation.** Production, main, the selected research kernel,
proof grammar and transcript remain unchanged.

## Decision from matched complete transactions

| Complete shape | Retained shared-gamma | Wide constant, late injection | Wide constant, early seed | Canonical constant |
|---|---:|---:|---:|---:|
| Transfer, current page | **1,025,815** | 1,034,194 | 1,032,698 | 1,026,560 |
| Transfer, rollover | **1,038,559** | 1,046,953 | 1,045,457 | 1,039,319 |
| Withdrawal, current page | **1,044,027** | 1,052,416 | 1,050,920 | 1,044,782 |
| Withdrawal, rollover | **1,057,043** | 1,065,415 | 1,063,919 | 1,057,781 |

Each cell is the maximum over the same three maximum-body proofs, not a
universal CU bound. Against each **identical proof**, the three variants
regress by **8,371–8,409**, **6,875–6,913**, and **737–775 CU**, respectively.
Early seeding saves exactly 1,496 CU against late injection in these twelve
proofs, but neither is competitive with the retained kernel. Fewer source-level
reductions do not imply lower metered CU; a specific spill/instruction-level
cause has not been established by these complete measurements.

All three 24-case matrices pass: accepted transfers/withdrawals in both page
shapes, plus supported malformed-proof/context/replay controls. The auditor
compares proof identity, fixture, authoritative-path fields, atomicity fields,
return-data hash/length, outcome and error against the retained build. Same Pool,
Registry and successful Token3.5 SBF, driver, runtime, account conditions and
**actual 1,200,000 CU TxV1 cap**. The driver CLI remains1400000; no diagnostic
limit override is used. Unsupported rollover stale/replay cases are not counted.

Because every maximum-body proof regresses, these rejected controls were **not**
expanded to ordinary-body and post-verifier failing-Token-CPI tests. Those
remain the retained winner's existing 50-case evidence, not new executions.
No selected binary or source was replaced by a losing control.

[Exact results and artifact pins](query-affine-results.json),
[reproducible auditor](experiments/audit_query_affine.py), and
[public evidence](evidence/query-affine/) record the three ELFs separately.
All were slightly larger than the retained 1,007,416-byte ELF:
+712, +568 and +120 bytes. Direct final r10 offsets remain≤4,096, with no
new emitted warning function. This limited static audit is not a complete
machine-stack theorem.

## Actual optimisation and rejected hypotheses

The selected packed query kernel decodes canonical C1/C2 once per record.
For each of 22×4 slots, it forms four 26-term mixed-field C1 dots, reduces their
limbs, then adds the prepared H/G/D three-product QM31 sum.

The first control keeps each C1 limb as its bounded seven-chunk raw sum,
injects those four numbers into the helper's nine raw channels, and performs
one QM31 reconstruction. The second installs the identical seed before the
three helper products, reducing its source-level live range. The third keeps
the original canonical C1 reduction and calls the already-selected
`qm31_add_sum_products3_prepared` instead of doing a separate QM31 addition.

Before compiler effects, both wide variants remove 352 full M31 reduction
calls and all three remove 352 canonical M31 additions. They add no field
products, but raw offset arithmetic, data movement and reduction placement
are real costs. The measured regressions reject these implementations, not
the algebra or all possible future lowerings.

Canonical parsing, rejection order, column/slot indices, prepared powers,
chord/fold operations, authentication and terminal comparisons are preserved.
The image gate, shifted ordinary rows, degree-q query batch and later relation
checks are not removed. There are no new or moved challenge requests,
transcript absorptions, proof values, nonces or hints.

## What the new Lean endpoint proves

[`QueryAffine.lean`](experiments/QueryAffine.lean) consumes pinned
SharedGammaDots, SemanticCarry, AffinePrimal and QmCrossRange dependencies.
It does not assume that the new helper equals the old one.

| Interface | Kernel-checked result |
|---|---|
| Actual C1 grouping | Six four-term chunks and final pair cover exactly indices0..25; partial reductions and balanced addition preserve the field sum |
| Raw C1 range | Every four-product chunk fits u64; seven partial folds give each limb≤75,161,927,666 |
| Balanced lowering | Every literal wrapping addition equals natural addition under that range |
| Helper products | Literal canonical decomposition/raw product casts and selected tower reconstruction are inherited; three fresh product prefixes remain in range |
| Wide injection | Four literal channel offsets reconstruct exactly the four raw constant limbs in the field |
| Early seed | The seeded channel recurrence equals late injection as natural channels; every seeded prefix fits u64 |
| Final result | `raw_affine_result` yields the explicit three-product tower sum with the C1 constant; `canonical_constant_equivalent` proves reducing that constant earlier gives the same result |

Writing `m=p-1` and `cap=7*(5*p+3)`, the new upper bound is

```text
3*m^2 + 4*cap = 13,835,058,330,160,070,612 < 2^64.
```

This is a **new wider-seed bound**, not the older canonical-constant bound
applied outside its hypotheses. The existing arbitrary-u64 partial-channel
reconstruction bound remains applicable after this injection.

The endpoint is kernel-checked source-shaped field/integer arithmetic, not
a translated Rust/LLVM/SBF refinement. Actual bit-operation lowering, Rust
representation and complete source correspondence retain their stated
boundary. Differential and complete execution tests supply distinct evidence;
no invented numerical compiler assumption is added to a soundness ledger.

Fifteen final axiom reports use only standard propext/Classical.choice/Quot.sound.
No retained theorem contains `sorry` or a new axiom. The first two leaf attempts
failed on vector-zero/cast inference and an overly general fold rewrite; v3
passed the late-injection endpoint. v4 adds the early-seed identity and range,
and is the final audited source. Failed logs are preserved and excluded from
the claim. No package replay, unchanged dependency replay, enlarged cap or
memory-pressure retry ran.

## Executed resources and provenance

| Focused job | Exit | Wall | Peak RSS | Swaps |
|---|---:|---:|---:|---:|
| Final QueryAffine Lean leaf | 0 | 6.73s | 2,948,612,096 bytes | 0 |
| Wide late Rust test | 0 | 23.11s | 516,400 KiB | 0 |
| Wide seeded Rust test | 0 | 23.03s | 518,348 KiB | 0 |
| Canonical Rust test | 0 | 22.70s | 516,196 KiB | 0 |
| Wide late SBF build | 0 | 34.28s | 593,228 KiB | 0 |
| Wide seeded SBF build | 0 | 34.58s | 593,036 KiB | 0 |
| Canonical SBF build | 0 | 34.28s | 593,660 KiB | 0 |

Each wide Rust gate compares 4,096 arbitrary bounded constants and canonical
helper triples, including all-maximal and zero inputs, against independent
canonical and naive-product references. It also compares 1,024 C1 raw profiles
against a u128 modular dot. All variants execute the packed-query controls:
512 canonical profiles, maximal limbs independent of a power sequence,
152 noncanonical positions and two short inputs. These are differential cases,
not exhaustive cryptographic games or measurements of 2^-100 events.

Lean4.32.0 uses the pinned cached Mathlib revision
`81a5d257c8e410db227a6665ed08f64fea08e997`. The runner checks source/olean
hashes of every imported research leaf. NUC jobs reuse the authorised task COPY:
HostRust1.94.1, SBF tools1.54, selected checked SBF Rust1.89-dev,
LiteSVM0.16.0/runtime4.2.1. Compilation dominates the Rust gate. Build scopes:
High5/Max7GiB, jobs2; SVM High3/Max4GiB; all SwapMax0.
Per-case SVM GNU-time logs are retained. Only public synthetic evidence was
copied back; no witnesses, proof binaries or ELFs are committed.

## Reproduce without modifying selected source

```sh
python3 docs/research/v8-no-work-100-20260907/experiments/audit_query_affine.py
python3 docs/research/v8-no-work-100-20260907/experiments/audit_query_affine.py --check-recorded
bash docs/research/v8-no-work-100-20260907/experiments/run_query_affine_lean.sh NEW_LOG
```

In the existing authorised NUC task COPY only:

1. Start from the pinned c3552659 selected source and field overlay
   SHA256 `bb4b177e4b06da631cef8cc3eaa44b3b08c1bbf3b123b975b116264f447d8fe0`.
   Apply `query-affine-field.patch` with zero fuzz. It adds a research-only cfg
   include; the resulting complete field hash must be
   `4d9a92f586b63485e1381653a1bc67d54dc20622a467aee4d0da20a571aeefca`.
2. For late/seeded controls, copy the archived
   `query_affine_arithmetic_v1.rs` to `query_arithmetic.rs`.
   Late uses `query_affine_field_v1.rs` at the included
   `query_affine_field.rs` path; seeded uses that path's current archived
   two-layout source. For canonical, apply `query-affine-query.patch` against
   c3552659's query source. The wide field include is cfg-disabled in this mode.
3. Run `check_query_affine_sources.sh MODE`. Run
   `run_query_affine_nuc.sh NEW_LOG`, setting
   `ASPIS_QUERY_AFFINE_SEEDED=1` or `ASPIS_QUERY_AFFINE_CANONICAL=1` as needed.
   Run `run_complete_build_nuc.sh MODE NEW_LOG` for the matching
   `query-affine`, `query-affine-seeded`, or `query-affine-canonical` mode.
4. Run `run_complete_matrix_nuc.sh MODE NEW_OUT` with
   `ASPIS_POOL_ZERO_FAST=1 ASPIS_COMPLETE_MAX_FIXTURES=1
   ASPIS_COMPLETE_TX_LIMIT=1200000 ASPIS_TOKEN_CONTROL=legacy35`
   and the pinned bundled Token ELF directory. No RPC or deployment.
5. Restore only the task-owned query source and reverse the exact field include
   patch after collecting evidence. This was done: selected query hash
   `57590907abf1c6a278cca0babc49b4c916a87a0a44e1f265b9bea28cc9fd52b1`
   and field hash `bb4b177e...` are restored. Cached measured ELFs remain distinct.

## Remaining frontier and next bounded experiment

The selected worst observed total remains **1,057,043 CU**, body
`697*16+52+24+22*621+2*296*26=40,282`. Headroom to1.2M remains142,957CU.
Current-page transfer beats the same-pool selected V7 control by15,008CU;
the other shapes remain4,158–8,159CU above it. This turn neither establishes
universal CU nor closes that no-regression requirement.

No new security term or positive grinding credit is introduced. Global recovery,
resource-bounded FS and adaptive full-view ZK remain separate open obligations.
There is no new prover-time, extractor-time or peak-prover-memory measurement.
The Solana testing skill kept the experiment on the matched Pool/Registry/Token
boundary and guided stopping expansion of losing candidates.

**Next experiment:** inspect the generated copying for the immutable
`[H_multiplier,G_multiplier,D_multiplier]` assembled inside each of four query
slots. If it is not already eliminated, construct that exact prepared array
once outside the slot loop (then consider once per query batch). Keep all three
outputs and canonical checks. This is a data-lifetime/representation test,
not another arithmetic reduction or a change to the checked relation.
A no-op lowering or any same-proof regression closes it; do not book an
assumed saving from source repetition alone.
