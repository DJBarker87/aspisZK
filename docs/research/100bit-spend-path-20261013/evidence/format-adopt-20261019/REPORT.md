# Adoption of the compact binary-multiproof proof format (2026-10-19)

Pre-registration: `design/PREREG-PROOF-SIZE-2-20261019.md` (items 1, 3, 4,
5, 6 here; item 2, the worst-case bound re-run, is a separate job).
Prototype: `evidence/proof-size-20261019/` (feature `compact-binary`).
Base: `research` at 931d81273. Branch `codex/r1-format-adopt-20261019`.
Host work dir: `/home/dombarker/project-offloads/codex-r1-format-adopt-20261019`.

UNPROVED: none of this is a security claim until the obligations in
`design/PROOF-SIZE-OBLIGATIONS-20261019.md` close.

## Verdict

The default build adopts the **57,607-byte compact binary-multiproof format**.
Measured criterion 1 passes on all six fixtures; the required verifier, Pool,
checkpoint, codec, ordered-trace, teeth, mutation and double-spend gates pass.
Criterion 2 (analytical worst-case bound) is explicitly **not run** here.
The P_R1 gate result is recorded below. This is not an overall six-criterion
PASS: the wallet's existing wire supports 3,763 rather than the requested
3,767 bytes with the measured transaction configuration (section 4), and the
full wallet suite has a baseline failure and a concurrency failure (section 5).

Code revision: `9a71031d3` (parent handover snapshot `0d64fd6d3`), based on
`931d81273`. The handover implementation was reviewed; its 27 changed source
files matched the host, then the audit/program guard was strengthened and
rebuilt. The refreshed wallet lock adds the three extracted writer crates.
Final source hashes include that lock (`source-hashes.json`). No Lean was run.

## 1. Source change (item 4: shipped default build)

`crates/aspis-r1-cost-probe` (the prototype's `compact-binary` feature is
removed; its code is now the default):

- `verifier::{tx1, tx2, tx2_authenticated, parse_shape}` are the compact
  binary-multiproof verifier (`candidate.rs`, re-exported), with
  `verifier::PROOF_BYTES = 57,607` and `verifier::SPLIT = 10` (stage 1
  accepts only split 10). These are the only R1 verification entrypoints of a
  default build. `View::proof_bytes` is renamed `View::eight_way_proof_bytes`
  (a layout figure for the retired format).
- The eight-way verifier (`View::parse`, per-query paths, `query`,
  `tx1/tx2/tx2_authenticated`) is moved unchanged into
  `verifier::eight_way` (`eight_way.rs`), compiled only with the new
  audit-only feature **`audit-eight-way`**. It never replaces a default
  name. `lib.rs` makes it a `compile_error!` together with `prover`, with
  the internal `program-build` marker, or on an SBF target
  (`target_os = "solana"`); receipts `guard-audit-with-prover` and
  `guard-audit-with-program` show the error. `private-leaf-salts` is now a default feature (the
  adopted format is defined only over salted leaves; building without it is
  a `compile_error!`), and `prover` implies it.
- Prover: `prove_from_semantics` is the prototype's compact prover (binary
  C1/C2/folded trees, compact semantic/`y1`, six zero-padded node slots);
  the eight-way and unsalted prover bodies are deleted, `Commitment` is
  binary-only, and `prove`, `prove_masked_fixture`, `prove_masked_attempt`
  and the retry loop `prove_masked_retrying[_with]` keep their signatures
  and emit only the new format (the `_candidate` entry points are removed).
- `dense.rs` reads the compact format with its own expansion, canonical
  scan and BTreeMap multiproof reconstruction (independent of the verifier's
  batch code; layout constants from `compact`).
- `sim.rs` (simE) still programs eight-way paths and emits the retired
  layout. Its two tests are `#[ignore]`d with a note citing
  PROOF-SIZE-OBLIGATIONS item 5 (section 6); nothing is deleted.
- Examples: `proof_size_s2` (teeth) is re-pointed at the default build (its
  eight-way control is a saved eight-way fixture); split 11 -> 10 in
  `masked_fixture_gate` (S2 only), `secure_attempt_gate`, `r1p_retry_gate`;
  `authenticated_tx2_gate` uses the compact opening offset. `proof_size_s1`
  and `native_gate` read or mutate the eight-way layout with the prover; they
  now require `prover` + `audit-eight-way`, a forbidden combination, so they
  are retained for the record but not buildable.

`programs/r1-cost-probe`: the `compact-binary` feature and the adapter shim
are removed; the adapter uses `verifier::PROOF_BYTES` and
`verifier::parse_shape`; `lib.rs` asserts `PROOF_BYTES == 57,607` and
`SPLIT == 10` at compile time. The release feature set is unchanged
(`pool-adapter,private-leaf-salts`). `[3, 11]` remains an admitted route; its
verification now always rejects (tested, no account written).
`r1_checkpoint_tests.rs` uses the regenerated transfer-1023 fixture; the
hash-call counts are asserted by a closed form (per batch and tree, three
leaf hashes per query plus `nodes + distinct - 1` parent hashes), and the
zero-progress checkpoint (`next = 0`) is now rejected by stage 2 after the
three resume hashes (the adopted stage 2 requires `next == SPLIT`).

`tools/r1-hash-input-counter`: default = adopted verifier (split 10);
feature `audit-eight-way` = eight-way verifier (split 11). Its `Cargo.lock`
loses the three optional-dependency edges of the removed `prover` feature
(fetched once, receipt `counter-fetch`).

The Pool program source is unchanged.

## 2. Fixtures (regenerated)

The six saved fixtures (`aspis-r1-rollover-measurement-20261019/fixtures/*`,
eight-way, 124,343 bytes) were re-proved with the adopted default prover:
same witness (`--pairs N`, kind), fresh OS entropy, split 10, by the
measurement driver (section 3). In every run the generated ASF8 statement
equals the saved fixture's statement byte for byte (`PROOF_SIZE_PUBLIC_MATCHES`
in each `receipts/adopt-*/stderr.log`; `public_equal_saved_fixture` in
`cu.json`), and the default verifier (tx1 split 10, strict tx2,
authenticated tx2) and the dense verifier accept natively before the SBF
replay. The new proofs and statements are committed under `fixtures/`
(proof data, 57,607 + 1,880 bytes each; the program checkpoint tests
include transfer-1023):

| Fixture | Proof bytes | Proof SHA-256 | Statement SHA-256 (= saved) |
|---|---:|---|---|
| transfer-13 | 57,607 | `55386c507d3feeeb...` | `f6bcd49446f1077d...` |
| transfer-255 | 57,607 | `fbc921ceb417aa22...` | `e201be4a028d7425...` |
| transfer-1023 | 57,607 | `832b4ae1a90c6e34...` | `72f067d263af326b...` |
| withdrawal-13 | 57,607 | `86623038d33f7fef...` | `43b4235fd9752c40...` |
| withdrawal-255 | 57,607 | `d92a261b2ba10c97...` | `7c2c27e135fa5377...` |
| withdrawal-1023 | 57,607 | `1c200eacfd8ea117...` | `456bcde525f9e694...` |

## 3. Compute (item 1)

Measured in LiteSVM 0.16.0, optimized driver, split 10, TxV1, release ELFs
pinned in `artifacts-sha256.txt`. The final host rebuild's Pool is byte-identical
to B1. All six fresh-generation runs and all six subsequent replays agree
exactly, including a further replay against the final guard-enabled verifier
and rebuilt Pool (`receipts/verified-reuse-*`, `runs/reuse-*/evidence.json`).
B1 references: `design/LEAD-REVIEW-POOL-B1-20261019.md` and its evidence.

| Fixture | Stage 1 B1 → adopted | Delta | Settlement B1 → adopted | Delta | Criterion |
|---|---:|---:|---:|---:|---|
| transfer-13 | 1,199,648 → 1,196,046 | -3,602 | 1,129,757 → 1,135,481 | +5,724 | PASS |
| transfer-255 | 1,199,567 → 1,198,152 | -1,415 | 1,161,066 → 1,166,524 | +5,458 | PASS |
| transfer-1023 | 1,199,687 → 1,192,314 | -7,373 | 1,160,974 → 1,166,269 | +5,295 | PASS |
| withdrawal-13 | 1,198,225 → 1,192,444 | -5,781 | 1,138,950 → 1,145,777 | +6,827 | PASS |
| withdrawal-255 | 1,198,264 → 1,192,575 | -5,689 | 1,170,523 → 1,175,735 | +5,212 | PASS |
| withdrawal-1023 | 1,198,386 → 1,194,056 | -4,330 | 1,170,263 → 1,173,313 | +3,050 | PASS |

Every stage 1 is ≤ B1 and every settlement is ≤ B1 + 10,000.
These are fixture measurements, **not** an upper bound over all proofs.
Original fixture mask entropy is explicitly `unknown-original-entropy` in
rollover evidence. Witness construction/setup seeds and statements are retained;
original mask/leaf secrets cannot be reconstructed from the saved proofs.
New mask and leaf secrets use fresh OS entropy, as in the prototype; identical
original mask seeds are not claimed.

## 4. Uploads (item 6)

The driver defaults to **3,767-byte chunks**; `--upload-chunk legacy` retains
900 bytes (TxV0 retains 800). This uses the measurement in
`evidence/proof-size-20261019/REPORT.md` section 4: TxV1 limit 4,096, lifecycle
write overhead 329, maximum 3,767. Re-measured by `receipts/upload-probe/`:
3,767 serializes to 4,096 bytes.

The wallet's existing tag-1 wire is `tag || offset:u32 || length:u32 || data`;
the R1 driver's tag-5 wire is `tag || offset:u32 || data`. With the same
accounts/signers/config, wallet overhead is **333**, so its maximum is
**3,763** (3,767 serializes to **4,100**, too large). The wallet therefore
retains the measured safe default 3,763, with explicit `ProofUploadChunkV1::Legacy`
(960 bytes). This is a recorded obstruction to the literal 3,767-wallet request,
not a claim that it passed. Changing the wire or transaction configuration
would require a distinct compatibility decision.

For either safe default, `ceil((688 + 57,607)/chunk) = 16` proof-body writes
and `ceil(1,880/chunk) = 1` statement write: **17 uploads per spend**.
Checkpoint bytes are reserved, not uploaded. This counts data uploads;
create/init/seal/spend transactions are additional. The admitted release route
rejects lifecycle loader tags, so this is an exact size/serialization count,
not a claim of a live-network upload. The wallet full-spend count and both
legacy/default reconstruction tests pass in `gate-wallet`.

## 5. Standing gates (items 3 and 5)

| Gate | Result / evidence |
|---|---|
| Codec | 1,233 outputs byte-identical to D70, SHA-256 `3ef16b12a329dd6d74b472cd75e5554c1ef8d98c618de3117f87b6c50d73e321`; `handover-verification.json` |
| Ordered trace | Audit verifier's 583 digest calls, checkpoint and counts equal D70 exactly. Repeated-input summaries compared as a multiset (HashMap iteration order). Adopted trace separately records its new binary-tree hash calls; equality with eight-way is not claimed. |
| Checkpoint/program | 33 tests pass, including 23 checkpoint cases; independently recompiled and rerun after program-build guard (`handover-program-recheck`). Compact bytes are hashed for checkpoint/resume. |
| Crate features | Default and audit: 16 lib + 14 integration tests each; detail-phases/optimized-terminal: 16; prover/r1p-check: 30 pass, 2 simulator tests ignored. |
| Pool suites | Default 87; R1/source-invariant features 118; all features 123; v7 candidate 123; each also passes 2 integration tests. Includes hint/marker authority/owner mutations. |
| Writer compiler differential | 2 tests: saved fixtures + 512 randomized witnesses + 2,046 mutations (31 kinds, 18 outcomes), shipped compiler equals retained reference (`gate-writer-migration`). |
| Masked/strict/authenticated | Transfer and withdrawal masked fixtures accepted; authenticated gate compares 9,253 trace entries with strict tx2 and rejects proof/public/checkpoint mutations. |
| Proof-size teeth | Compact/default + dense accept; all pre-registered mutations reject, including padding, compact canonicality, wrong split, old-format input, changed stored proof, checkpoint hashing expanded bytes and nonzero omitted high halves (`gate-teeth`). |
| Retry P_R1 | **8/8 accepted and verified with strict tx1+tx2 and dense**, then retry loop accepted in 1 attempt and verified. `r1p-retry-gate.json`, `receipts/gate-r1p-retry/`. Forced-rejection/retry unit tests also pass. |
| Runtime replays/mutations | All 19 final-ELF scenarios pass their expected outcomes. Six fixture successes, both kinds' double spends (with/without 1-lamport prefunding) reject with `0x41532026`; rent-prefunded success, wrong release, stale lane, proof rejection and withdrawal CPI rollback tested (`scenario-results.json`, `runs/`). |
| Stack | Both strict audits PASS; every warned oversized/overwrite function absent from complete linked ELF symbols and relocation targets; no surviving oversized frames, overwrites or unparsed diagnostics (`stack/`). |
| Forbidden features | `audit-eight-way+prover` and native program dependency + audit fail with the intended compile_error (exit 101). SBF target additionally guarded. |
| Simulator | Explicitly ran ignored verification test: **fails Err(Parse)** on adopted format (`gate-simulator-obligation5`). Both layout-dependent tests remain ignored with PROOF-SIZE-OBLIGATIONS item 5 / section 6 citation. This remains an open obligation. |
| Wallet | New upload tests pass; full run: 187 lib pass, 2 fail; all 33 integration tests pass. See failure analysis below. |

Wallet failures: `fixed_suite_known_answer_roundtrips_and_recomputes_commitment`
has the identical left/right bytes with the base `931d81273` builder, verified
by a separate baseline crate (`wallet-known-answer-baseline`).
`atomic_file_reopens_and_replaces_the_exact_durable_forest` failed with
`MigrationInProgress` in the parallel suite, then passed alone with one test
thread (`wallet-durable-serial`). The parallel failure is retained, not waived
as a full-suite PASS. No unrelated wallet source was changed to mask either.

Failed pre-handover attempts are retained: stale removed-feature selection
(`check-1`), stale wallet/counter lockfiles, and initial checkpoint/hash-counter
test failures in `prior-failed-receipts/`; their corrected runs are in
`receipts/`. Handover evidence comparison initially failed because it compared
unordered HashMap summaries as lists; the corrected comparison sorts only
those summaries and still compares all ordered calls exactly. No unchanged
full regression was repeated. Rebuild/replay during review was justified by
the new program-build guard and missing final artifact/verification evidence.

## 6. Pins

`artifacts-sha256.txt` records full SHA-256, sizes, features and toolchains for
both adopted ELFs and their complete unstripped links. Verifier:
`8cf8d84ed0fe340a190b4f40a9f953f0e0523370299ba3ec8bbed9d65b88ace3`.
Pool: `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`
(byte-identical to B1). Native Rust 1.94.1; SBF cargo-build-sbf 3.1.13,
platform-tools v1.52, Rust 1.89.0-dev / LLVM 20.1.7. Build features and every
changed code/manifest/lock hash are pinned separately in `source-hashes.json`.
No executable artifacts or signing keys are committed. Host keys are retained.

All work ran on the assigned host in optimized builds with `-j 4`, separate
systemd scopes, MemoryHigh 6G, MemoryMax 8G, MemorySwapMax 0 and TasksMax 64.
The maximum simultaneous task reservation was below 55 GiB (at most three
8-GiB scopes for this task); no other worker's job was stopped.
All completed receipts report zero swaps. `run-summary.json` indexes exits,
wall times, peak RSS and cgroup limits. `final-evidence-validation` checks
all changed source hashes, final-ELF CU rows, 19 scenarios, 8/8 retry result and
both strict stack audits. Codec stdout (16,431,699 bytes) stays on the host;
its exact hash, length and final line are committed in lieu of the large log.

## Remaining

- Item 2's analytical worst-case bound re-run is a separate job after landing.
- Exact 3,767-byte wallet chunk requires reconciling its extra length field or
  its transaction configuration; safe measured 3,763 already meets 17 uploads.
- Original saved proof mask secrets/seeds are unavailable; identical public
  statements and witness/setup construction are verified, identical old mask
  seeds are not.
- Simulator binary-layout refinement (obligation 5) and all other formal
  PROOF-SIZE-OBLIGATIONS remain open; this Rust/SBF job closes none of them.
- The two wallet suite failures above remain explicitly recorded.

## Runs

Receipts under `receipts/` (command, exit, wall, peak RSS, swaps, cgroup
limits) per host run. `#print axioms`: N/A, no Lean in this job.
