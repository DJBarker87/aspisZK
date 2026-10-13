# P2 to first named stage: CU reconciliation

This is an accounting comparison of the P2 S2 transfer diagnostic with the first named optimized stage, `pairing`. It uses the exact recorded remaining-CU markers; it does not make a source-equivalence or cryptographic claim. The comparison uses the same proof/public bytes, S2 split, runtime versions, heap, and elevated diagnostic limit.

## Result

For this matched S2 transfer measurement, recorded total-transaction savings are **679,500 CU in tx1** and **893,354 CU in tx2**, or **1,572,854 CU over the pair**. The receipts do not show approximately 1.1M CU saved in each transaction. P2 totals are 2,441,407 / 2,411,848 CU; pairing totals are 1,761,907 / 1,518,494 CU. The 356 CU per-transaction harness overhead is the same on both sides, so the same deltas hold for verifier program CU.

The approximately 1.1M figures do reconcile to **P2 → final D18**:
1,109,841 CU in tx1 and 1,129,503 CU in tx2. They include all four subsequent
optimization transitions, not only the first `pairing` stage. These are the
same diagnostic fixtures; they are not the newer full-mask Pool measurements.

## Original P2 phase format

Phase deltas are summed from each raw marker interval. Pairing subdivides semantic evaluation and each query into `*-part` markers; those intervals are summed into the original P2 buckets. The `account-write` interval is included in `Checkpoint write`, matching `REPORT-P2.md`. “Saved” means P2 minus pairing; a negative value means pairing used more CU.

| Phase / metric | P2 tx1 | Pairing tx1 | Saved tx1 | P2 tx2 | Pairing tx2 | Saved tx2 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Parse | 56,875 | 51,123 | +5,752 | 36,136 | 30,384 | +5,752 |
| Semantic | 903,170 | 808,024 | +95,146 | 0 | 0 | +0 |
| Prepare | 489,141 | 156,408 | +332,733 | 0 | 0 | +0 |
| Checkpoint read | 0 | 0 | +0 | 114,865 | 108,629 | +6,236 |
| Merkle | 100,280 | 100,300 | -20 | 120,355 | 120,391 | -36 |
| Query folds and rho accumulation | 822,065 | 576,776 | +245,289 | 983,707 | 692,073 | +291,634 |
| Relation rounds and pairing | 0 | 0 | +0 | 1,059,165 | 527,554 | +531,611 |
| Final rho evaluation | 0 | 0 | +0 | 94,175 | 36,015 | +58,160 |
| Checkpoint write | 68,211 | 67,611 | +600 | 1,783 | 1,786 | -3 |
| Entry/exit and other overhead | 1,309 | 1,309 | +0 | 1,306 | 1,306 | +0 |
| Program subtotal CU | 2,441,051 | 1,761,551 | +679,500 | 2,411,492 | 1,518,138 | +893,354 |
| Other transaction overhead CU | 356 | 356 | +0 | 356 | 356 | +0 |
| Total transaction CU | 2,441,407 | 1,761,907 | +679,500 | 2,411,848 | 1,518,494 | +893,354 |

P2 marker totals and pairing marker totals each reconcile exactly to the recorded program subtotal: tx1 2,441,051 / 1,761,551 CU; tx2 2,411,492 / 1,518,138 CU. Whole-transaction totals add a fixed 356 CU each. Across tx1+tx2, program subtotal is 4,852,543 CU for P2 and 3,279,689 CU for pairing; reduction is 1,572,854 CU.

## Provenance and matched inputs

| Item | P2 baseline | First named stage (`pairing`) |
| --- | --- | --- |
| Worktree / revision | `/Users/dominic/ZK/.worktrees/r1-precheck-p2`, branch `codex/r1-precheck-p2-20261010`, commit `d2197e35589ee075a61c2a22aa9b88300f464517`, source revision `19d8f2023c615954ff0ad2fa981c6c03e96bf506` | NUC build source revision `7742957648c33cf045eb6a672e7c7cc796b61087+pairing+a7c365534f43f5c508adf4d5b598d5af9059d0cfe74d0f95eff9bc6a4932b16c` |
| Source manifest | [`P2 manifest copy`](evidence/p2-cu-reconciliation/p2-source-manifest.json), file SHA-256 `36310a183acd32c8b6ffdac6292ab6f77e43a0406bf8e279c714256c7e5312ef` | [`pairing source manifest`](evidence/latest/results/100bit-path-20261013/pairing/source-manifest.json), source-manifest SHA-256 `a7c365534f43f5c508adf4d5b598d5af9059d0cfe74d0f95eff9bc6a4932b16c` |
| SBF ELF SHA-256 | `1ec08e2381f401900f7d78fadb688e28b50ffd25395d3d478164b82436283457` | `9f0ea93e3aea66cf47d5561893ead22203d7cba4b4f2d3d4abeb60b3aa4d5004` |
| Build | `cargo build-sbf --manifest-path programs/r1-cost-probe/Cargo.toml --sbf-out-dir results/r1-precheck-20261010/S2/bin -- --locked`; recorded [`P2 SBF build`](evidence/p2-cu-reconciliation/p2-s2-sbf-build.json). P2 report says native binaries used optimized release profile. | `cargo build-sbf --manifest-path programs/r1-cost-probe/Cargo.toml --sbf-out-dir <pairing>/bin -- --locked -j 2`; exact receipt [`pairing SBF build`](evidence/latest/results/100bit-path-20261013/pairing-sbf.json) |
| Runtime / diagnostic | Agave `4.2.1`, LiteSVM `0.16.0`, heap `262144`, elevated diagnostic limit `200000000` CU | Agave `4.2.1`, LiteSVM `0.16.0`, heap `262144`, elevated diagnostic limit `200000000` CU |
| Transaction instruction limit | `1400000` CU recorded in runtime metadata | `1400000` CU recorded in runtime metadata |
| Fixture proof / public | `122231` bytes / `123480a04a2da763351ab3ef779e7cf8a9ffd0c91169d5b0674e5751b73ca080`; public `1880` bytes / `d2241c5432fa3d5b34084c06e9c3f510cc61542a793287aad471287563761557` | `122231` bytes / `123480a04a2da763351ab3ef779e7cf8a9ffd0c91169d5b0674e5751b73ca080`; public `1880` bytes / `d2241c5432fa3d5b34084c06e9c3f510cc61542a793287aad471287563761557` |
| S2 shape | variant `2`, two folds, final `64`, k `10`, 22 queries | variant `2`, two folds, final `64`, k `10`, 22 queries |
| Checkpoint | `2824` bytes; tx1 and tx2 hashes preserved in JSON | `2824` bytes; tx1 and tx2 hashes match P2 |
| Feature selection | Probe/program/statement Cargo manifest hashes match `pairing` exactly; build report identifies P2 package. No `optimized-terminal` feature in P2 Cargo feature list. | `cargo build-sbf` command has no explicit `--features`; program default `custom-heap`, probe default empty, and explicit dependencies `aspis-core:r0` and `aspis-statement:r0,pool-v1-kernel`. The probe/program/statement Cargo manifest hashes match P2 exactly at `pairing`; `optimized-terminal` is absent. |
| Field implementation source | `crates/aspis-core/src/field/wide_exact.rs` hash `a262dfa32003f1661ee95d44de29ac885e745070fb88b41552d2b4cac31a1a96` | same source path hash `56c26ce33cd0caee95f33474bfc351c5409503b6af665dba7c8837d6ec1068ea` (changed); shared `field.rs` hash is `3046536d04e84357c7df7bd742ec9839d1e1dc47ccc0ecaa59eb79ddec453c68` |

Both fixture metadata records identify deterministic fixture-only K-tail samples via rejection sampling. Equal proof/public hashes establish only that the exact bytes were reused in these measurements. The field implementation source hash changed; no formal or semantic equivalence claim is made. P2 Cargo manifest hashes for the probe, SBF program, and statement crate are identical to the pairing manifest hashes, so this first stage does not add a Cargo feature bundle.

The diagnostic hashes the checkpoint account **after** each transaction.
The two transactions have different checkpoint hashes because tx2 changes its
status and checksum. The comparison checks equality between implementations
at each of those two states, not equality of the pre- and post-tx2 states.

## Source-change trail

Changed paths below are derived from per-stage source-manifest hash comparison, restricted to the probe crate, the core `wide_exact.rs` file, and the probe SBF program. Total changed manifest paths include changes outside this filtered set. These path lists identify what changed; they do not assign semantic equivalence.

| Transition | Total manifest path changes | Relevant probe/core/program paths | tx1 CU | tx2 CU |
| --- | ---: | --- | ---: | ---: |
| P2 → pairing | 124 | `crates/aspis-core/src/field/wide_exact.rs`, `crates/aspis-r1-cost-probe/src/fast_domain.rs`, `crates/aspis-r1-cost-probe/src/fast_dots.rs`, `crates/aspis-r1-cost-probe/src/fast_pairing.rs`, `crates/aspis-r1-cost-probe/src/lib.rs`, `crates/aspis-r1-cost-probe/src/r1_semantic.rs`, `crates/aspis-r1-cost-probe/src/r1_wire.rs`, `crates/aspis-r1-cost-probe/src/sampler.rs`, `crates/aspis-r1-cost-probe/src/transcript.rs`, `crates/aspis-r1-cost-probe/src/verifier.rs`, `crates/aspis-r1-cost-probe/src/weights.rs`, `crates/aspis-r1-cost-probe/tests/domain_equivalence.rs`, `crates/aspis-r1-cost-probe/tests/dots_equivalence.rs`, `crates/aspis-r1-cost-probe/tests/pairing_equivalence.rs`, `crates/aspis-r1-cost-probe/tests/sampler_equivalence.rs`, `crates/aspis-r1-cost-probe/tests/validated_prefix.rs`, `crates/aspis-r1-cost-probe/tests/weights_equivalence.rs`, `programs/r1-cost-probe/src/lib.rs` | 1,761,551 | 1,518,138 |
| pairing → terminal | 2 | `crates/aspis-r1-cost-probe/Cargo.toml`, `programs/r1-cost-probe/Cargo.toml` | 1,523,042 | 1,518,138 |
| terminal → rho-clean | 8 | `crates/aspis-r1-cost-probe/Cargo.toml`, `crates/aspis-r1-cost-probe/examples/native_gate.rs`, `crates/aspis-r1-cost-probe/src/dense.rs`, `crates/aspis-r1-cost-probe/src/prover.rs`, `crates/aspis-r1-cost-probe/src/r1_semantic.rs`, `crates/aspis-r1-cost-probe/src/transcript.rs`, `crates/aspis-r1-cost-probe/src/verifier.rs` | 1,411,984 | 1,379,425 |
| rho-clean → geometry-dots | 4 | `crates/aspis-r1-cost-probe/src/fast_dots.rs`, `crates/aspis-r1-cost-probe/src/fast_pairing.rs`, `crates/aspis-r1-cost-probe/src/verifier.rs`, `crates/aspis-r1-cost-probe/tests/dots_equivalence.rs` | 1,331,527 | 1,282,676 |
| geometry-dots → d18 | 5 | `crates/aspis-r1-cost-probe/src/dense.rs`, `crates/aspis-r1-cost-probe/src/transport.rs`, `crates/aspis-r1-cost-probe/src/weights.rs`, `crates/aspis-r1-cost-probe/tests/transport_equivalence.rs` | 1,331,210 | 1,281,989 |

The table CU columns are the one-run S2 transfer diagnostic program costs from `RESULTS-FIT.md`; “terminal”, “rho-clean”, “geometry-dots”, and `d18` are subsequent selected stages, not independent P2 comparisons. At `pairing → terminal`, the two changed Cargo manifests add the documented `optimized-terminal` feature bundle (the nine `aspis-statement` audit features listed in `RESULTS-FIT.md`). Successive measured reductions were pairing→terminal 238,509 / 0, terminal→rho-clean 111,058 / 138,713, rho-clean→geometry-dots 80,457 / 96,749, and geometry-dots→d18 317 / 687 CU (tx1 / tx2). The rejected `fast-accumulator` stage measured 1,341,002 / 1,294,080 CU, which is 9,792 / 12,091 CU more than d18. Stage evidence is listed in [`RESULTS-FIT.md`](RESULTS-FIT.md).

## Reproduction and limits

Run `python3 docs/research/100bit-spend-path-20261013/validate_p2_cu.py`
from the worktree root. The root-reviewed script reconstructs every phase
from the four raw remaining-CU marker streams and checks the published JSON,
program subtotals, transaction totals and savings. This check passes.

Baseline raw diagnostic receipts are copied at [`P2 tx1`](evidence/p2-cu-reconciliation/p2-transfer-tx1.json) and [`P2 tx2`](evidence/p2-cu-reconciliation/p2-transfer-tx2.json); pairing receipts are [`pairing tx1`](evidence/p2-cu-reconciliation/pairing-transfer-tx1.json) and [`pairing tx2`](evidence/p2-cu-reconciliation/pairing-transfer-tx2.json). Fixture metadata is copied alongside them. The original P2 report is retained at [`REPORT-P2 copy`](evidence/p2-cu-reconciliation/REPORT-P2.md); the S2 SBF build and diagnostic-command receipts are copied alongside it. The pairing diagnostic receipt records the exact remote command and NUC path. No new builds or measurements were run.

This is a diagnostic cost reconciliation, not a capped acceptance outcome. It records no settlement, privacy, soundness, or release-gate conclusion.
