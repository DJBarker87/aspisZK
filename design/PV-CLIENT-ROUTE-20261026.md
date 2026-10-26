# Proof-account client route audit — 26 October 2026

**STOP / owner escalation: selected route is not adopted by the operational R1
client. Target not yet established.** No shipped implementation is changed here.

Audit baseline: `a0c5e1f66a9d16f76a22bd77fb0bc499a64a9978` (`research`), branch
`codex/pv-client-20261026`. The release ledger is read-only. “Shipped” below
means checked-in operational entry points, not an attestation of an installed
binary. The ledger does not pin an adopted client executable or Python bundle.

## Entry-point inventory

The operational R1 client is the `devnet_spend` binary in package
`aspis-r1-cu-probe` (`tools/r1-cost-probe/Cargo.toml:2`), driven by
`scripts/r1_devnet_spend.py:9,167`. The script permits a configured `signer`
path; its default is `native-target/release/devnet_spend`. The default Cargo
binary `aspis-r1-cu-probe` is a probe, not this client. The selected *library*
caller is in crate `aspis-r1-cost-probe`, exported behind `r1p-check`
(`crates/aspis-r1-cost-probe/src/lib.rs:25`). Neither export nor a crate name
establishes client adoption.

| Entry point / source location | Prover route | Release significance |
|---|---|---|
| `devnet_spend::main`, `tools/r1-cost-probe/src/bin/devnet_spend.rs:13–15`; planner action `plan.rs:70,112` | `prove_masked_retrying` → `StateOnlyAttemptSecrets::generate` at `crates/aspis-r1-cost-probe/src/prover.rs:334`; 96-byte draw | Operational R1 transfer/withdrawal runner; **not D162 target**. `plan.rs:120,123` uses a separately supplied proof account for publication. |
| `RealR1_client::prove_for_proof_accounts`, `crates/aspis-r1-cost-probe/src/RealR1_client.rs:20,27–28` | `prove_masked_retrying_with` + `generate_for_mask_nonce(proof_account(k))`; public nonce and 64 private bytes | Selected D162/D186/D187 library route, not wired into the operational planner. |
| Public R1 APIs, `crates/aspis-r1-cost-probe/src/prover.rs:51,82,105,327,354` | `prove`/`prove_masked_fixture`: deterministic fixtures; `prove_masked_attempt`: caller-supplied secrets/store; generic retry: 96; callback retry: caller-selected | Only the concrete selected callback fixes the 64-byte proof-account route. Generic APIs remain available. |
| `pool_gate`, `tools/r1-cost-probe/src/bin/pool_gate.rs:1492,1510–1513` | Fixture or OS96 single `prove_masked_attempt` | LiteSVM Pool/proof measurement harness, not selected client. |
| R1 examples `proof_size_s2:23`, `masked_fixture_gate:46`, `authenticated_tx2_gate:20` under `crates/aspis-r1-cost-probe/examples/` | Deterministic `prove_masked_fixture` | Fixture proofs, not deployment evidence. |
| R1 example `secure_attempt_gate.rs:43–46,66–81` | Initial OS96 single attempt; selected-nonce replay probes | Replay checks do not make its first proof selected64. |
| R1 example `r1p_retry_gate.rs:52–54,89` | OS96 single attempts and generic96 retry | Research retry/performance gate. |
| R1 historical examples `native_gate.rs:34`, `proof_size_s1.rs`; `readbudget_count.rs:70–72` | Deterministic / retired eight-way or candidate APIs | Manifest records historical unbuildable combinations/missing `compact-binary` feature; not operational releases. Other R1 examples inspect semantics/folds or simulate, not user spend production. |
| Profiling entry `tools/prover-speed-20261022/speed_profile.rs:16–17` | 64 private bytes with OS-generated public nonce | Not a retained proof-account callback/client. |
| CLI `aspis-xtask v6-honest-proof` / `v7-honest-proof`, `xtask/src/main.rs:180–195`, `xtask/src/v6_release.rs:359–363,471–475` | Public proof-account nonce, 64 private bytes → V6/V7 onefold production builders | **Other protocol**, not R1 callback/retry/proof format. |
| Live client crate `tools/v7-live-pool-proof/src/lib.rs:63–71,93–101` | `generate_for_mask_nonce(plan.attempt_id)` → V7 pair-forest transfer/withdrawal onefold | **Other protocol**; wallet adapter binds attempt ID to proof account (`crates/aspis-pool-wallet-v1/src/live_pool_witness_adapter_v2.rs:673,811`). |
| `tools/v7-txv1-honest-proof/src/main.rs:100–112` | `build_v7_pair_forest_transfer_fixture_mined_v1` → deterministic fixture seeds (`crates/aspis-prover/src/v7_pair_forest_fixture.rs:351–353`) | Mined V7 fixture, not selected R1. Its upload-request binary `src/bin/build_proof_upload_requests.rs:104` reads existing payload, does not prove. |
| CLI V5 artifact builder, `xtask/src/spend_devnet/v5.rs:4166`, `xtask/src/v5_cu_probe.rs:1371` | V5 runtime-bound production demo body | **Other protocol**. Older spend execute/readiness/upload commands consume existing artifacts; they do not become selected R1 by submitting them. |
| `aspis-prover` example `spend_production_miner.rs:221` → `state_only_spend.rs:1003–1010` | OS96 bounded first-good/mined state-only spend | **Other protocol**, 17 attempts, not R1 eight-attempt route. |
| `aspis-prover` example `spend_fixture.rs:81–83`; `tools/v8-state-only-cu-probe/src/main.rs:118` | Deterministic spend fixture / low-level state-only proof | **Other protocol**. `spend_complete_good_product` and `spend_soundness_epro_ledger` analyze saved artifacts, not selected R1 spend generation. |
| Lower-level `aspis-prover` APIs `src/lib.rs:288–735`, `src/r0.rs:70`, `src/state_only_proof.rs:167,212`, `src/v6_onefold_prover.rs:1778–2100` | Generic stage/R0, state-only, V6/V7 production/fixture builders with caller data | Library building blocks, no automatic R1 client-route binding. |
| Wallet crate `crates/aspis-pool-wallet-v1/src/live_pool_witness_adapter_v2.rs:4–5`; examples `tx_v1_devnet_probe`, `tx_v1_simulation_request` | Witness/request/account/upload construction | No spend prover invocation; external V7 handoff above is distinct. On-chain programs verify/settle, not produce user proofs. |

Inventory covers checked-in `crates/`, `tools/`, `xtask/`, `scripts/` and
`programs/`; copied evidence, tests and parked experiment snapshots are not
additional shipped clients. This is source inspection, not a formal whole-program
call-graph or installed-binary census.

## Release identity and selected experiment

`design/RELEASE-LEDGER-20261025.md:214` explicitly keeps this route open and
client64 parked. Lines 225–243 pin on-chain artifacts, not a host client:

| Artifact | SHA-256 (historical release pin, not freshly reproduced) |
|---|---|
| Default verifier | `f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4` |
| Devnet verifier | `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299` |
| Pool | `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548` |

D162 decision 1 selects **public nonce = retained proof-account key**, with only
two private 32-byte seeds. `state_only_entropy.rs:202` implements that draw;
`generate()` instead chooses all three blocks. D186/D187's R1 host result is
the selected library caller, durable ledger and fail-closed duplicates, with
verifier untouched. `REAL-R1-20261023.md` stage 6 explicitly says this is a
library caller/control instance and is not yet wired into a network client.
`RealR1_client_tests.rs:24–29,48–55` exercises direct/adapter paths and native
Rust verifiers, plus duplicate failure. It never loads a pinned verifier ELF.
Historical all-three-ELF reproduction is artifact identity, not execution of
this client's proof through that ELF.

The headline's `rust : FSExperiments ...` must be instantiated by the complete
execution of the adopted client invoking
`aspis_r1_cost_probe::RealR1_client::prove_for_proof_accounts` →
`StateOnlyAttemptSecrets::generate_for_mask_nonce` →
`aspis_r1_cost_probe::prover::prove_masked_retrying_with` →
`prove_masked_attempt`/private prover body, including errors, ledger effects,
key policy, publication and observer events. The present operational planner
does not instantiate that selected execution. A function name alone cannot
instantiate `RustRealRefinement`: the actual `rust.real`, `rust.observe`,
randomness law and `RunJoin` must be supplied at these source/artifact pins.

## Gaps and minimum owner proposal

1. No adopted selected64 operational caller or pinned deployed client bundle.
2. Proof-account selection is disconnected from entropy in the current runner;
   a separately published account key does not repair the nonce law.
3. No current client-to-pinned-ELF proof-account integration receipt, and no
   artifact-level exclusion of the generic96 fallback.
4. R1 native control evidence retains public prefix/hash binding, initial/retry
   invariant, reachable R2/R3 body, cleanup/Drop/error effects, E1/E2 and exact
   experiment marginals. Retain seed/fuel/query-scan obligations and all
   L1/L2/L3 observer obligations; do not weaken `simE` or the observer.
5. Final client/native/compiler/features/CPU identity, native refinement,
   identical-coin 1000 whole-prover comparisons, quiet median <15s and H5
   slowdown <=10% remain adoption gates (release ledger:227–228).

**Minimal wiring change, proposed only:** change
`tools/r1-cost-probe/src/bin/devnet_spend/plan.rs` to call the existing selected
adapter using retained per-attempt keys, choose exactly `attempts - 1` for
stage1/settlement, and change `scripts/r1_devnet_spend.py` to allocate/persist
that mapping before proving and use its selected key for create/upload.
Add a small account-policy helper and Python retention/resume helper; update
`scripts/r1_devnet_inventory.py` plus inventory helper to discover every new
key/recovery path. Keep rejected, unused, fatal and interrupted keys/ledgers;
fail closed on ambiguous resume/duplicates/IO errors, with no generic fallback.
The reviewed candidate already proposes this implementation; do not duplicate
or merge it here.

This minimum touches **tools/ and scripts/, no crates/ or programs/**. The
current job explicitly stops before implementation/adoption; no three-ELF
rebuild is triggered by this documentation. If final native prover integration
changes any crates/ or programs/, all three ELFs must be rebuilt and match the
pins, or stop and escalate. Historical identities alone cannot satisfy that
changed-source gate. Owner escalation is required by this task's step 3 and
the frozen-implementation instruction in `pv-common.txt`.

## Integration receipt required before adoption

Pin by SHA-256 and size: exact client binary, Python bundle/helpers, manifests,
Cargo.lock, selected caller/prover/entropy/ledger closure, compiler/flags/features,
verifier/Pool ELF and program IDs; record source revision and dirty hashes.
Exercise actual planner and selected callback for transfer and withdrawal, with
the resulting successful nonce/key used for account creation, upload, stage1
and settlement against the pinned ELF in a controlled runtime. Record actual
acceptance and protected-state effects, not just native `verifier::tx1/tx2`.
Include rejection then success/eighth-attempt mapping, duplicate and durable
failure, exhaustion/entropy failure, interrupted/error resume and retained state.
Use source/call reachability checks plus exact built-feature/binary association
to exclude generic96 from this shipped entry, including fallbacks; other
exported library APIs can remain. No runtime acceptance or absence theorem
is claimed in this audit. Keep every funded/refundable/authority key securely.

## Premise delta and validation

Before: deployment requires “client uses selected proof-account route.” After:
**same requirement, unsatisfied by the audited operational planner**. No Lean
statement, quantifier, event, bound, trust field or deployment premise is removed,
added or weakened. This checked source-routing counterexample is the task's
stop condition; spending Lean/Kani budget cannot repair a different caller.

Informs release-ledger rows “Selected proof-account client route and caller-error
behavior” (:214), “Representable statement domain and publication/observer
association” (:215), “Real-prover refinement” (:207), and “Prover rewrite
adoption” (:227), plus E1/E2 and L1/L2/L3 rows. Removes **none**. No
`design/PRIVACY-LEDGER-20261026.md` exists at the baseline; these exact row
names/exact deployment condition identify the lead's prospective rows.

Validation is source/document inspection only so far. No Lean attempt, Kani
run, Cargo check/test, host scope, proof generation, ELF execution, chain/RPC,
wallet-secret read or key operation ran. Formal axioms/resource receipts are
N/A. Candidate review and reproducible source hashes follow in the next stage.
