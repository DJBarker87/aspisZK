# Housekeeping receipt (2026-10-20)

Branch: `codex/cx-housekeeping-20261020`. Input revision:
`74f689738905518e54f8532eaf368e333cefbf16`. No push, Lean build, SBF build,
stage-2 work, key cleanup or deployment. Existing evidence and historical
bodies are unchanged; only new evidence is added.

## Wallet lock and suite

Host workspace: `/home/dombarker/project-offloads/codex-cx-housekeeping-20261020`.
Native Rust/Cargo 1.94.1; commands are in the scripts and individual JSON
receipts. `cargo generate-lockfile --offline` resolved 351 packages from the
host cache; **no network fetch**. Tests use `--release --offline --locked -j 4`
and one test thread (the prior durable-store parallel interference is recorded
in format-adoption evidence). Time was spent in compilation and wallet tests,
not proof generation or elimination. No source fixes were made.

Every launch used `systemd-run --user --scope -p MemoryHigh=6G
-p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64`. Scope IDs are in
`scope*.log`. Host capacity was 62 GiB / 54 GiB available at preflight;
no competing user build scope was listed. The later full populated-cgroup
reservation snapshot (`reservation.json`) totals 32.375 GiB including our
8 GiB, below the 55 GiB safe limit. RSS below is GNU time's maximum child
RSS, not aggregate cgroup peak; swap counts are zero, swap cap is zero.

| Attempt | Exit | Wall seconds | Peak RSS KiB | Swaps |
|---|---:|---:|---:|---:|
| default-complete-snapshot | 101 | 33.501 | 661048 | 0 |
| default | 101 | 35.988 | 558244 | 0 |
| eight-lane-complete-snapshot | 101 | 25.798 | 878756 | 0 |
| eight-lane | 101 | 0.981 | 190332 | 0 |
| integration-default-affinity4 | 0 | 8.660 | 537652 | 0 |
| integration-default | 101 | 9.014 | 538136 | 0 |
| integration-eight-lane | 0 | 23.188 | 759964 | 0 |
| lock | 0 | 0.322 | 112268 | 0 |

Final results: default library **121 pass / 1 fail**; eight-lane library
**188 pass / 1 fail**. Default integration **12 pass**, eight-lane integration
**33 pass**, across all six integration targets. The sole library failure is
`tests::fixed_suite_known_answer_roundtrips_and_recomputes_commitment`
(`src/lib.rs:713`), the **pre-existing note-context known-answer vector**.
Its left/right assertion bytes match the B1 base control exactly:
`../pool-b1-20261019/receipts/test-wallet-base-control-1/stdout.log` (base
`ba385a751`, exit 101); also reproduced by format-adoption's
`wallet-known-answer-baseline` at base `931d81273`. This job compares those
existing baseline bytes; it does not claim a fresh baseline run. The suite
is not reported as fully green. No tests were skipped to hide the failure.

Retained setup failures: first lock launch exit 127 (Cargo absent from
systemd PATH; `receipts-path-preflight/`); initial tests exit 101 because the
source snapshot omitted tracked `refine/diffharness/tests/glue_gen.rs`.
Added the missing tracked input and reused the compiled cache. Initial default
integration exit 101: parallel lld thread creation hit TasksMax=64
(“Resource temporarily unavailable”). Retry changed CPU affinity to 0–3
via `taskset`, retaining -j 4 and all caps; it passed. Eight-lane integration
passed without retry. The failed receipts are retained.

## Per-file changes

| File | Change |
|---|---|
| `SECURITY.md` | Prepend dated B1/master `create_with_seed` pointer; retain original body verbatim. |
| `aeneas-verif/v7-pool-nullifier-marker-source-20260830/README.md` | Prepend dated B1/master `create_with_seed` pointer; retain original body verbatim. |
| `crates/aspis-statement/src/pool_v1/README.md` | Prepend dated B1/master `create_with_seed` pointer; retain original body verbatim. |
| `docs/research/100bit-spend-path-20261013/design/G_R1_9-POOL-SPLIT-CHECKPOINT-20261015.txt` | Prepend dated B1/master `create_with_seed` pointer; retain original body verbatim. |
| `docs/research/100bit-spend-path-20261013/design/J1-ORACLE-CALL-INVENTORY-20261015.md` | Prepend dated B1/master `create_with_seed` pointer; retain original body verbatim. |
| `docs/research/100bit-spend-path-20261013/design/J1-R16-R19-RUNTIME-RELEASE-20261015.txt` | Prepend dated B1/master `create_with_seed` pointer; retain original body verbatim. |
| `docs/research/100bit-spend-path-20261013/design/J1-RELATION-STATEMENT-20261015.md` | Prepend dated B1/master `create_with_seed` pointer; retain original body verbatim. |
| `docs/research/100bit-spend-path-20261013/design/J1-SELECTED-PATH-HASH-BOUNDS-20261015.md` | Prepend dated B1/master `create_with_seed` pointer; retain original body verbatim. |
| `docs/research/100bit-spend-path-20261013/design/POOL-PDA-STUDY-20261019.md` | Prepend dated B1/master `create_with_seed` pointer; retain original body verbatim. |
| `docs/research/pool-v1-prepared-settlement-kernel-20260826.md` | Prepend dated B1/master `create_with_seed` pointer; retain original body verbatim. |
| `docs/research/v7-pool-eight-lane-concurrency-gate-20260827.md` | Prepend dated B1/master `create_with_seed` pointer; retain original body verbatim. |
| `docs/research/v7-pool-nullifier-marker-atomic-lifecycle-20260830.md` | Prepend dated B1/master `create_with_seed` pointer; retain original body verbatim. |
| `docs/research/v7-pool-runtime-adversarial-audit-20260830.md` | Prepend dated B1/master `create_with_seed` pointer; retain original body verbatim. |
| `docs/reviews/mathematical-status-20260814.md` | Prepend dated B1/master `create_with_seed` pointer; retain original body verbatim. |
| `programs/aspis-pool/README.md` | Prepend dated B1/master `create_with_seed` pointer; retain original body verbatim. |
| `release/preflight/v5-production-freeze.md` | Prepend dated B1/master `create_with_seed` pointer; retain original body verbatim. |
| `crates/aspis-pool-wallet-v1/Cargo.lock` | Offline host regeneration; 49 lines added / 43 removed, including compatible cached transitive version refreshes and the five8_core 1.0.0 dependency split. |
| `docs/research/100bit-spend-path-20261013/design/R1-PREMISES-REACCEPTANCE-20261020.md` | Draft P1–P7, exact artifact/tool pins and main-ledger lines; flag R1-only details and unresolved verifier pin drift. No acceptance asserted. |
| `docs/research/100bit-spend-path-20261013/evidence/housekeeping-20261020/` | New scripts, receipts, reservation, ledger provenance, annotation checks and this report; no binaries. |

The section-6 `.lean` models and `results/` historical evidence were not
edited; the Aeneas README carries the R1 supersession pointer. Relative note
links resolve, and stripping the five-line notes recovers every historical
body exactly (`annotation-check.json`). No new premise or theorem is added.

## Lead decisions still owed

Accept P1–P7 at step 9 against the final selected verifier/source/formal
manifest. P4/P5 are not explicit in the V5 ledger. Keep X1's B1 freshness and
blocking premises outside target (T). The adopted verifier `8cf8d84e…` and
runtime-gated stage-2 candidate `0622ad3f…` are distinct; source extraction,
refinement and release runtime observation remain as documented in the draft.
The stronger stored-bump-implies-canonicality target is false: the existing
noncanonical lane test in `programs/aspis-pool/src/pair_forest.rs:3937–3967`
is its counterexample. The draft retains F6 provenance instead.
