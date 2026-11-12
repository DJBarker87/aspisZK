# pv-aspis-rewrite: the gates rerun after the rebase onto the frozen source (2026-11-12)

The branch was rebased from ea0e8bd91c3 onto the frozen release source
3d700effcabe1dbf2d3ceaa3aaa469fcdfb955de (`future-version`). This file records the rerun of the
gates of `README.md` on the new base.

* BEFORE = 3d700effcabe1dbf2d3ceaa3aaa469fcdfb955de plus the gate tool
  `tools/r1-cost-probe/src/bin/pv_bytes_gate.rs` as it is at 40226f091c4 (the tool is not in the
  frozen commit; the file is the same in both trees).
* AFTER = 40226f091c434cd2ee871c5bd680bcb8d66cab28.

These are tests on fixtures. They show that the listed outputs are the same bytes before and after
on the inputs that were run; they state nothing about inputs that were not run, and no theorem is
stated here. No soundness or privacy claim changes. Target not yet established.

Status: gate A, gate B and the test suites ran and show no difference other than the new tests of
the branch. **The timing gate is pending: waiting for a quiet host** (see the end).

Host directory `/home/dombarker/project-offloads/codex-pv-aspis-rewrite2-20261112`. Receipts are in
`rebase-gates-20261112/`: `host/` (scripts), `host-runs/<job>/` (receipt, target, time log, cgroup
values per job), `gates/{before,after}/` (ELF tables, proof tables, test outcomes),
`gates/COMPARE.txt`.

## What the branch changes

`git diff 3d700effcab 40226f091c4 --stat` outside `evidence/`: 10 files, 1178 insertions, 39
deletions. No file under `programs/` is changed.

| file | compiled for the SBF programs |
|---|---|
| `crates/aspis-prover/src/state_only_hiding.rs` | no (`aspis-prover` is not a dependency of any program) |
| `crates/aspis-r1-cost-probe/src/RealR1_client.rs` | no (feature `r1p-check`) |
| `crates/aspis-r1-cost-probe/src/RealR1_client_tests.rs` | no |
| `crates/aspis-r1-cost-probe/src/prover.rs` | no (feature `prover`) |
| `crates/aspis-statement/src/constraints_v4.rs` | **yes** (the module of `sparse_eq_weights`, as the first README says) |
| `crates/aspis-statement/src/pool_v1/pair_forest_hiding.rs` | no (`cfg(not(target_os = "solana"))`) |
| `crates/aspis-statement/src/pool_v1/pair_forest_trace.rs` | no (same) |
| `crates/aspis-statement/src/pool_v1/pair_tree_hiding.rs` | no (same) |
| `crates/aspis-statement/src/state_only_semantic.rs` | no (same) |
| `tools/r1-cost-probe/src/bin/pv_bytes_gate.rs` | no (host tool, new file) |

The column was checked in two ways: from the `cfg` attributes and manifests, and from the compiler's
own dependency lists of the SBF builds (`gates/*/sbf/<program>/dep_sources.txt`, taken from cargo's
`.d` files). Of the ten files, only `constraints_v4.rs` appears in any list; it appears in the lists
of the two verifier builds, pool, registry and the legacy `aspis-verifier`, and not in upload's.

The two source copies on the host differ in exactly the nine crate files above
(`src_before_vs_after.txt`). They were exported with `git archive` of the two revisions, restricted
to the directories the builds need (the same set of paths as the first run's source copy).

## A. Program ELFs

Recipe of the frozen build (`evidence/future-version-20261111/host/fv_build_adapter_src.sh`, and
`fv_pool_build.sh` for the Pool): cargo-build-sbf 3.1.13, platform-tools v1.52, offline, `--locked`,
`-j 4`, clean environment with the same `CARGO_*` variables, devnet identifiers
`ASPIS_R1_POOL_PROGRAM_ID=37hdATMkskKX1hiCWhz4nnzkD7GauYwX8EQwcpUDb3Zt` and
`ASPIS_R1_REGISTRY_PROGRAM_ID=9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q` for the verifier. The
deployed feature string is `aspis`, read from `cmd.txt` of the frozen build (`out/fz1`) on the host.
Each tree was built in its own source directory with its own cargo target directories, so nothing
was shared between the two builds. Jobs `B-before-sbf`, `B-after-sbf`.

| program | features | sha256 before | sha256 after |
|---|---|---|---|
| verifier (`programs/r1-cost-probe`), deployed set, devnet identifiers | `aspis` | 827aaec1cbd92e37767d3d76b9fc6174ef2851a498e2e7935e1b55bc68ccb12b (969,328 bytes) | the same |
| verifier, two-transaction set, devnet identifiers | `pool-adapter,private-leaf-salts` | 84e13ece4affef88e4d74f1836e09fb93d8991d9ed773d3051799e52409b3051 (1,570,104 bytes) | the same |
| upload | none | 9b2ab3d41695d81bfb79b93931d9323515fcc28a35fd725253be5e41bdc45874 (25,992 bytes) | the same |
| pool | `r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit` | 0553a8bd5ef5c5ff93023b1923f96f9651a23f5aa4e50855baebe29109799cec (340,320 bytes) | the same |
| registry | default | 7ad46f0d4b102a7c9699149d23bf6e065b6151feeaca95977d0a3146167d01ab (209,280 bytes) | the same |
| `aspis-verifier` (legacy) | default | does not build (`E0432`, unresolved import `aspis_statement::pool_v1`) | the same failure |

The BEFORE verifier ELF equals the frozen program ELF 827aaec1…. The Pool ELF equals the other
session's Pool builds of the frozen source (`out/PL-frz-a`, `out/PL-frz-b` on the host, 0553a8bd…).
Both `sbf` jobs exit 1 because of the legacy `aspis-verifier` alone; the other five exit codes are 0.

One thing that does not match and was looked into: the frozen build's `source_tree.sha256`
(27e7316a…) is not reproduced by the same formula on the BEFORE tree (3ccac264…,
`gates/before/sbf/source_tree_frozen_formula.sha256`). The frozen build's source directory
`src-fz1` differs from commit 3d700effcab in seven files of `crates/` and `programs/`, in comment
lines only (46 changed lines, none outside a `//` comment). The later directories `src-frz-a` and
`src-frz-b` of that session have `crates/` and `programs/` identical to the BEFORE tree. The ELF is
the same in all cases.

Limits: the legacy `aspis-verifier` is not covered, because it does not build on either tree.

## B. Proof bytes

Tool `pv_bytes_gate`, release build with `r1p-check`, toolchain 1.94.1 (binary sha256 before
bad91358…, after f15c9bff…; jobs `B-*-native`). Jobs `G-{before,after}-{table,retry,fail}`.

| table | rows | sha256 before | sha256 after | `cmp` |
|---|---|---|---|---|
| fixture: transfer and withdrawal, seeds 1 to 16, pinned format then re-packed | 32 proofs, all accepted | 8c95088cae342b1591ff1d679d8c878318cf664176fa50ec5f2cd563d7f937ce | the same | identical |
| retry: seeds 17 to 20, fixture prover and retry loop on a fresh ledger, then a second call | 8 + 8 proofs, 8 duplicate rejections | baa0d6db06ead3aca405ea47d8a90736b231cfcf0f9dc59c3778772b6c8598d0 | the same | identical |
| failing paths, seeds 1 and 2 | 20 rows | 38463a01ec6d41da4440a0bf79cff08f17c0dba645a9525f05ee1d2951399f9f | the same | identical |

The three files are also byte-identical to the tables of the first run on the old base
(`host-evidence/gates/base2/`), so the rename of the frozen commit changed no proof byte on these
inputs. What the tables do not cover is unchanged from the first README: every first attempt was
accepted, so no row goes through a rejected attempt followed by another one.

## C. Tests

`cargo test --release --offline --locked --no-fail-fast`, toolchain 1.94.1, whole suites; the
commands are in `gates/*/tests/<suite>.cmd`, every test with its outcome in `<suite>.outcomes`.
Jobs `T-{before,after}-<suite>`.

| suite | before: passed / failed / ignored | after | difference in the outcome lists |
|---|---|---|---|
| `aspis-core` (`r0`) | 313 / 0 / 1 | 313 / 0 / 1 | none |
| `aspis-statement` (`r0,pool-v1-kernel`) | 291 / 0 / 0 | 296 / 0 / 0 | five new tests, all pass |
| `aspis-prover` (`r0,insecure-spend-fixture`) | 237 / 2 / 20 | 238 / 2 / 20 | one new test, passes |
| `aspis-r1-cost-probe` (`r1p-check`) | 95 / 0 / 0 | 97 / 0 / 0 | two new tests, both pass |
| tool `tools/r1-cost-probe`, bins `devnet_spend` and `pv_bytes_gate` (`r1p-check`) | 7 / 0 / 0 | 7 / 0 / 0 | none |

Failing tests, the same two before and after (test file `r0_semantics` of `aspis-prover`):
`public_bytes_match_independent_p1_fixture`, `equal_circle_points_reject_without_resampling`.

New tests in the AFTER tree (the whole difference between the outcome lists, `gates/COMPARE.txt`):
`constraints_v4::pv_aspis_rw_tests::pv_aspis_rw_sparse_eq_weights_matches_pin_body`,
`pool_v1::pair_forest_hiding::tests::pv_aspis_rw_endpoint_counts_matches_pin_body`,
`pool_v1::pair_forest_trace::pv_aspis_rw_tests::pv_aspis_rw_copy_registry_matches_pin_body`,
`pool_v1::pair_tree_hiding::tests::pv_aspis_rw_endpoint_counts_matches_pin_body`,
`state_only_semantic::tests::pv_aspis_rw_copy_helper_sum_matches_pin_body`,
`state_only_hiding::tests::pv_aspis_rw_balance_m31_matches_pin_body`,
`RealR1_client::tests::nonce_array_transfer`, `RealR1_client::tests::nonce_array_withdrawal`.

## Timing gate

**Pending: waiting for a quiet host.** `host/timing_wait.sh` is running on the host. It starts the
five interleaved rounds (seed 3, binaries `before` and `after`, one capped scope) only when the
1-minute and 5-minute load averages are both under 2, and gives up 90 minutes after the end of the
other gates (09:42 UTC, so at 11:12 UTC). At the time of writing the load was about 5 from other
jobs. No timing figure is reported from the loaded runs above. The result, or "not run", will be
appended here.

## Resources

Every job ran in its own user scope `pvar2-<job>` with MemoryHigh 6G, MemoryMax 8G, MemorySwapMax 0,
TasksMax 256, after `~/streamb-slots/turn.sh` and the reservation check, admitted at the first
attempt each time. Two scopes at a time (one per tree). Largest cgroup memory peak: 2.66 GiB
(`T-before-prover`); SBF builds 2.2 GiB. Swaps 0 in every job. The longest jobs were the prover
suites, 1 h 07 min each, of which one test binary takes 3,093 s.

## Differences from the first run

* Base 3d700effcab instead of ea0e8bd91c3; the verifier's deployed set is `--features aspis`
  instead of the sixteen `future-*` names. The first run's hashes for the verifier (7a77273b… and
  3c5463f0…) and the Pool (e0e49c34…) belong to the old base and are not expected here; upload and
  registry have the same hashes as in the first run.
* The two trees were built in separate source and target directories (the first run reused one
  source path and its target directories), so every unit was compiled for both trees.
* Builds and tests were pinned to CPUs 12-15 (before) and 16-19 (after) instead of 0-3, which the
  other session's slots use.
* Test counts at the base moved with the base: core 312 to 313, statement 279 passed and 1 failed
  to 291 passed and 0 failed (`pool_v1::format::tests::format_binding_pins_existing_primitives`
  now passes on both trees), probe 88 to 95. The prover and tool counts are as in the first run.
* All base suites compiled at the first attempt; no replacement runs were needed.

## Changes to the gate scripts (all forced by the new directory or the renames)

* all scripts: work directory `codex-pv-aspis-rewrite2-20261112`; source directory, tag and CPU
  list are parameters; cargo target directories are per tag.
* `sbf_all.sh`: feature string `aspis` in place of the `future-*` list (from the frozen build's
  `cmd.txt` and the rename map); build names `verifier-aspis` and `verifier-twotx`; added the
  frozen build's source hash formula, `lock.sha256`, the tool version, and the dependency source
  list per program.
* `tests.sh`: writes the command and a sorted per-test outcome list; the `z4` suite entry, which
  the first run did not use, is dropped.
* `run_job.py`: work directory and scope prefix (`pvar2-`).
* `chain.sh` replaces the first run's several chain scripts (one chain per tree);
  `timing_wait.sh` and `collect.sh` are new.
* No change to `pv_bytes_gate.rs` or to any rewritten source.

## Not done

* The timing gate (pending, above).
* The translation and Lean check runs of the first README (its section D) were not rerun.
* The `z4` crate's tests and the Kani harness were not run, as in the first run.
* Nothing was deleted on the host. Nothing was pushed.
