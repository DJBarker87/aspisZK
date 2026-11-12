# pv-aspis-rewrite-20261111: prover functions rewritten so that Charon and Aeneas translate them

Branch `codex/pv-aspis-rewrite-20261111`, cut from `future-version` at ea0e8bd91c3. Host directory
`/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111`.

What this is. Six prover-side functions were rewritten, one client entry was added, and two functions
were examined and left alone. The gates below are tests on fixtures. They are not a proof that the old
and the new code are equivalent, and nothing here states or proves a theorem. No soundness or privacy
claim changes. Target not yet established.

No on-chain program source was changed. The files touched are in `crates/aspis-statement` (three modules
compiled only off-chain, and `constraints_v4.rs`, which is compiled for the programs too),
`crates/aspis-prover`, `crates/aspis-r1-cost-probe` (`prover.rs`, `RealR1_client.rs` and its test file),
and one new tool binary. `rewrites.diff` is the whole diff against the base.

## Per function

Notes: `notes/01` to `notes/09`. "Translates" means: tool k2 (sha256 7271db7e...) emits a body with no
error for that function from the LLBC that Charon 0.1.223 makes of the rewritten source; "Lean" means the
emitted text elaborates in a check file against the compiled objects of package g2.

| # | function | commits | translates | Lean |
|---|---|---|---|---|
| 1 | `endpoint_counts` in `pair_forest_hiding` and `pair_tree_hiding` | edbab03e842 | yes, both | yes, standard axioms only |
| 2 | `build_pool_v1_pair_forest_copy_registry_v1` (+ `first_link_of_kind`) | d62d3c13664, 7e255bd09b8 (test only) | yes | yes; see the limit below |
| 3 | `apply_mask_material_for_layout`, `balance_m31_copy_inactive` (+ six helpers) | 855bf7f47eb, d5f8c0caa38 | yes, fourth form | yes; opaque std items `core.mem.take`, `Vec::default`, `slice::Iter::any` |
| 4 | `state_only_copy_helper_sum` | 9b1066b9d5a | yes | yes, standard axioms only |
| 5 | `sparse_eq_weights` (+ three helpers) | 1d001c3d4f6, c1dc3a54ad1 | yes, third form | yes; opaque std items of the `rev().take_while().count()` chain |
| 6 | `record_check_times` removed; `public_check` writes to a log passed by the caller | 09b7dfd74f8 | `public_check` yes; its callers no, see below | `public_check` yes; opaque `p_r1_check` and the type `R1CheckTimes` |
| 7 | `p_r1_check` | not changed | | |
| 8 | `prove_for_proof_account_nonces` added beside the unchanged `prove_for_proof_accounts` | eb2028bc633 | the provider `attempt_secrets` yes; the entry no, see below | provider yes; opaque `getrandom` and `zeroize` items |
| | `points_from_alphas` | not changed (verifier side) | | |

Forms that did not translate, with the exact message, are in notes 03 and 05 and in
`host-evidence/host-runs/A-i3-*`, `A-i3b-*`, `A-i3c-*`, `A-i5-*`, `A-i5b-*`.

### Limits of the translation results

* Item 2. The registry builder's own text elaborates. It calls
  `build_pool_v1_pair_forest_copy_row_schedule_v1`, and that function's emitted text does not elaborate
  against the Lean library of the package: the instance of `Iterator` it needs has the fields `filter`
  and `collect`, which the library's `Iterator` structure does not have (run `L-c2-copy_registry-1`,
  three errors, the third for `position`). The translator warns about the same three items. In the
  passing check (`c2b`, `c2c`) the schedule builder is the package's axiom. So `endpoint_counts` no longer
  blocks the schedule builder, but the schedule builder is still not usable in Lean; its
  `.into_iter().filter(..).collect()` is the cause. It was not on the list and was not changed.
* Item 2, `sorryAx`. The registry in the check depends on `sorryAx`. It comes from a definition already in
  package g2, `pair_tree_hiding.build_pool_v1_pair_copy_row_schedule_v1_loop0` (run
  `L-c2c-copy_registry-diag-1`), not from a block of this job.
* Items 6 and 8. Tool k2 rejects the signature of every function that has a parameter of type `HashFn`
  (`fn(&[&[u8]]) -> [u8; 32]`) with "We don't support arrow types with locally quantified regions". This
  is a property of the tool and not of the new code: a control run on three functions that are unchanged
  from the pin (`prover::tail_samples`, `fixture_secret`, `folded_leaves`; run `A-k-hashfn_control`) gives
  the same message for each, and for `aspis_core::state_only_private_merkle::private_leaf_hash`. Package g2
  has `prove_masked_attempt`, `retry_attempt` and the others from its base emission, made by another tool
  (aeneas-pvfix3), which prints the parameter as `hash : Slice (Slice Std.U8) -> Result (Array Std.U8
  32#usize)`. That tool was tried on this job's LLBC and aborts (run `AF-i68-check_times_client`, exit 2,
  uncaught `Not_found`), so this job has no emission of the new `_timed` functions from either tool. The
  reported error on `prove_for_proof_accounts` has the same cause; a first-order argument in place of the
  closure does not remove it.
* `prove_from_semantics` and `prove_masked_with_attempt` gained one parameter. They were not re-emitted
  (same `HashFn` rejection under k2).
* The check files compare nothing with the Rust: they show that the emitted text is accepted by Lean.

## Gates

Base = ea0e8bd91c3 plus the gate tool. Final = 7e255bd09b8. Host runs, one capped user scope each
(MemoryHigh 6G, MemoryMax 8G, MemorySwapMax 0, TasksMax 256) after `streamb-slots/turn.sh` and the
reservation check; receipts in `host-evidence/host-runs/`. The cap for cargo is the same 6G/8G: the
largest peak of any cargo job here was 2.6 GiB resident (prover tests); the scope peak of the SBF builds was 2.2 GiB.

### A. Program ELFs (`host-evidence/gates/{base,after1,final}/sbf/`)

Recipe of `docs/r1/BUILD.md` (cargo-build-sbf 3.1.13, offline, locked, `-j 4`), same source path and
same cargo target directories before and after.

| program | features | sha256 before | sha256 after |
|---|---|---|---|
| verifier (`programs/r1-cost-probe`), branch head set, devnet identifiers | `pool-adapter,future-one-tx-lean,private-leaf-salts,future-fast-kmul,...` (in `cmd.txt`) | 7a77273b1dc64689a0eed1cc267c6e81c9f6d0ad2e17fe0be316243d3ae9a3d5 | the same |
| verifier, pinned set, devnet identifiers | `pool-adapter,private-leaf-salts` | 3c5463f0bc12d15e0eff8f3999b375bb92c7861775a550280ae4da91c1725edc | the same |
| upload | none | 9b2ab3d41695d81bfb79b93931d9323515fcc28a35fd725253be5e41bdc45874 | the same |
| pool | `r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit` | e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc | the same |
| registry | default | 7ad46f0d4b102a7c9699149d23bf6e065b6151feeaca95977d0a3146167d01ab | the same |
| `aspis-verifier` (legacy) | default | does not build at the base (unresolved import `aspis_statement::pool_v1`) | the same failure |

The "after" build that recompiled is `after1` (c1dc3a54ad1): `aspis-statement` and every program crate
that depends on it were recompiled and the five ELFs came out identical. The `final` run found every unit
fresh: the one file that differs between `after1` and `final` is `pair_forest_trace.rs` (one line inside
a `cfg(test)` module), and that module is not compiled for SBF. The first hash equals the other session's
build X1 of the same source.

So no function on the list is reachable from a program under these feature sets in a way that changes a
byte. That includes `sparse_eq_weights`, whose module is compiled for the programs. The legacy
`aspis-verifier` is not covered, because it does not build.

### B. Proof bytes (`host-evidence/gates/{base2,after1,final}/table-*.txt`)

Tool `tools/r1-cost-probe/src/bin/pv_bytes_gate.rs`, release build with the client's feature `r1p-check`.

| table | rows | base2 sha256 | after1 | final |
|---|---|---|---|---|
| fixture: `prove_masked_fixture` then `to_summed_format`, transfer and withdrawal, seeds 1 to 16 | 32 proofs, all accepted | 8c95088cae342b1591ff1d679d8c878318cf664176fa50ec5f2cd563d7f937ce | identical | identical |
| retry: seeds 17 to 20 through the fixture prover and through `prove_masked_retrying_with` with derived secrets on a fresh durable ledger, then a second call on the same ledger | 8 + 8 proofs, 8 duplicate rejections | baa0d6db06ead3aca405ea47d8a90736b231cfcf0f9dc59c3778772b6c8598d0 | identical | identical |
| failing paths, seeds 1 and 2 | 20 rows | 38463a01ec6d41da4440a0bf79cff08f17c0dba645a9525f05ee1d2951399f9f | identical | identical |

Each row has the sha256 of the proof in the pinned format (57,607 bytes) and re-packed (55,815 bytes).

What the tables do not cover. Every first attempt was accepted in every row, so no row went through a
rejected attempt followed by another one. Failing paths that were forced: the secrets source failing at
attempt 0 (`Entropy`, nothing reserved), a variant other than S2 (`Semantic` before any attempt), a reused
nonce (`Semantic` at the reservation, ledger unchanged), the fixture prover with a variant other than S2.
The row meant for "entropy failure after a rejection" shows an accepted proof, because attempt 0 was
accepted. "Attempts exhausted" and a rejected check cannot be forced from outside the crate: verdicts are
forced only by its `cfg(test)` hooks. Those paths are in the crate's library tests (`prover_retry_tests`,
suite `probe` below), which pass before and after.

### C. Wall time (`host-evidence/gates/timing-after1.txt`, `timing-final.txt`)

`pv_bytes_gate time`: `prove_masked_fixture` alone, seed 3, one proof per operation per call, the two
binaries alternating in one scope, five rounds. Host load average 1.1 to 1.4 during both runs (the earlier
table runs were made under a load near 19 and are not timing evidence).

| run | operation | base2, seconds | rewritten, seconds | median base2 | median rewritten | change |
|---|---|---|---|---|---|---|
| after1 | transfer | 38.497 38.432 38.420 38.396 38.312 | 38.501 38.454 38.551 37.821 38.282 | 38.420 | 38.454 | +0.09% |
| after1 | withdrawal | 38.080 38.339 37.754 37.923 37.662 | 37.914 38.170 38.340 37.565 37.877 | 37.923 | 37.914 | -0.03% |
| final | transfer | 38.176 38.240 38.307 38.428 38.225 | 37.738 38.079 38.034 37.851 38.076 | 38.240 | 38.034 | -0.54% |
| final | withdrawal | 37.765 37.837 37.845 38.322 37.629 | 37.747 37.815 38.218 37.743 37.898 | 37.837 | 37.815 | -0.06% |

Within the +10% limit; the differences are inside the spread of the runs.

### Tests (`host-evidence/gates/*/tests/`)

`cargo test --release`, toolchain 1.94.1, whole suites.

| suite | base: passed / failed / ignored | final | new tests | failures |
|---|---|---|---|---|
| `aspis-core` (`r0`) | 312 / 0 / 1 | 312 / 0 / 1 | 0 | none |
| `aspis-statement` (`r0,pool-v1-kernel`) | 279 / 1 / 0 | 284 / 1 / 0 | 5 | `pool_v1::format::tests::format_binding_pins_existing_primitives`, before and after |
| `aspis-prover` (`r0,insecure-spend-fixture`) | 237 / 2 / 20 | 238 / 2 / 20 | 1 | `r0_semantics`: `public_bytes_match_independent_p1_fixture`, `equal_circle_points_reject_without_resampling`, before and after |
| `aspis-r1-cost-probe` (`r1p-check`) | 88 / 0 / 0 | 90 / 0 / 0 | 2 | none |
| tool `tools/r1-cost-probe`, bins `devnet_spend` and `pv_bytes_gate` (`r1p-check`) | 7 / 0 / 0 | 7 / 0 / 0 | 0 | none |

The three failing tests fail at the base in the same way and are not touched by this job. The tool's bin
`r18_replay` does not compile as a test at the base (a `litesvm` method it calls does not exist), so the
tool suite was restricted to the two bins named. Base runs: `base` (statement), `base2` (core, tool),
`base3` (prover, probe, on a separate copy of the base tree).

## D. Translation runs (`host-evidence/gate-d/`, `roots/`)

Charon run `C-<tag>`, tool run `A-<tag>`, Lean run `L-<check>-1`. `gate-d/llbc.sha256` and
`emissions.sha256` have the hashes of the LLBC files and of the emitted Lean files; the files themselves
stay on the host. `gate-d/check/<check>/RwCheck.lean` is each check file with `mkcheck.json`, the list of
carried blocks with their hashes. The emissions were made from the source copy `src-rw`, which was
compared with the gate source `src` by `diff -rq` before the gates (`sync-after1.log`, `sync-final.log`).
The emissions of items 1, 2, 4, 6 and 8 were made before the second forms of items 3 and 5 and before the
test-only change to item 2; the functions they concern did not change after that.

## Runs that told nothing, and what replaced them

* `G-base-table-1`: cut by its one-hour timeout under load after 15 proofs. Replaced by `G-base2-*` with
  fewer seeds per run.
* `T-base-core`, `-prover`, `-probe`, `-tool`, and `T-base2-prover`, `T-base2-probe`, `T-after1-prover`,
  `T-after1-probe`: did not compile for want of input files outside the first source copy (`results/`,
  three `tools/` paths, two `docs/` paths), or because of `r18_replay`. Replaced after adding the files.
* `T-after1-statement`: the new registry test failed on its own coverage threshold (889 and 743 against
  a threshold of 1000); every equality in it had held. Threshold corrected in 7e255bd09b8, `T-final-statement`.
* `B-final-sbf`: recompiled nothing, as explained under gate A.
* `AF-i68-check_times_client`: the other tool aborts, as explained above.

## Not done

* Gates were run on the whole set of rewrites together (`after1`, `final`), not once per function. Since
  every gate passed on the whole set, no bisection was needed.
* No per-function Charon run of the base source: the base errors are the ones recorded by the earlier jobs.
* The Kani harness `prover_commit_balance7::balance_m31_caller`, whose subject
  `balance_m31_copy_inactive` was rewritten, was not run in this job. It was run
  afterwards and reached its time limit with no verdict, as its only earlier run
  did on the pin body; see the correction in `notes/03-apply_mask_material.md`.
* The `z4` crate's own tests were not run (no file of it was changed).
* Nothing was spliced into a package; package g2 is unchanged.
* The on-chain program autofixer was not run: no program code was written or changed.
* Nothing was deleted on the host. Nothing was pushed.
