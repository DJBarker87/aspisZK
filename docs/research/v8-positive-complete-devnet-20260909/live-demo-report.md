# Repaired V8 COMPLETE: local and devnet result

The genuine positive transfer **1,000 → 600 + 400** finalized on Solana devnet at slot **495745019**. Exact signed simulation and confirmed atomic settlement both consumed **1,105,880 CU**, against **1,200,000 declared CU**. [Finalized transaction](https://explorer.solana.com/tx/3bVzMRjY9GbkMgTtA9AQXU2U5LEtcRjHhGQ5brbc3DXqyLezhuYR6xE51dfF7EhTUHTqPM4sjo5uYNK38brY7eFa?cluster=devnet).

This establishes live engineering functionality only. Global recovery, payment/source refinement, Fiat–Shamir and full-view ZK remain under formalisation. The changed mask distribution is not a completed privacy proof. No production activation or soundness completion is claimed.

## Revision and artifact provenance

Research base: `e90e7338656f221c9a1bbde90d533ba94d002014`; preceding deployment infrastructure: `6a32de2656002fb9ab6160f37c4a9b3d9bc993a8`; integration/local-gate commit: `ba29d3510416ad10ef1a1297448ae1f50b98605c`. This report and final evidence are committed subsequently on `research/v8-positive-complete-devnet-20260909`. The enclosing commit is the final evidence revision (`git log -1 --format=%H -- docs/research/v8-positive-complete-devnet-20260909`). No merge or push was performed.

The original selected optimized COMPLETE ELF `3d07a23833bac533f791b7ce2d619f4cd40aff6e1b5314c3b43be596b38c15a3` was authenticated against the frozen NUC artifact in the preceding experiment. This run rebuilds that integration with the committed opt-in positivity repair, new profile/release framing and fresh verifier binding. It is **not byte-identical** to that ELF. The seven upstream source snapshots, `prepare_integration.py`, `integration-inputs.json` and `check_inputs.py` record and verify changed inputs. Previous input manifests and failures are preserved.

The additional lane94 residual checks the inverse product of both output amounts at row1014/column3. The active-cell mask overwrite changes the effective inventory from3803 to3802. Its descriptor binds the prior COMPLETE profile as parent, which differs from the standalone upstream host run's default V7 parent. Host derivation checks the frozen107-byte SBF descriptor and32 arbitrary QM31 packing cases. QM31, q22, current domain, canonical fields, maximum body40,282, carried image gate, shifted ordinary rows and shifted query batch remain enabled. No favourable-transcript search was used.

| Artifact | Bytes | SHA256 |
|---|---:|---|
| `sbf-complete-terminal-stack/aspis_v8_complete_sbf.so` | 962312 | `f4290a2206320a5273a6b1948e396aa140c2c29af65d692b5c93bd4842e1012c` |
| `local-artifacts/pool-checkpoint-fix.so` | 537728 | `e07dc1e7445a0256c6da7a9833e7946cc0225e9076db1dd350f914dac500d108` |
| `local-artifacts/registry.so` | 193416 | `76f4c382de8c638084cd3c15d50398224e5ad377eeebfbc15d6f35a61f0f045d` |
| `demo-host-target/release/aspis-v8-devnet-tools` | 926560 | `c9b033abf80e402f8aac6d5afdea5e1aa56578b6368aa14734f4756a8cb7ca52` |
| `docs/research/v8-no-work-100-20260907/experiments/performance-host/target/release/aspis-v8-performance-host` | 1541968 | `c50800b3dcd189c94aaa9774fdbc3a068b71b172ea306c3c3c78e058082fdd78` |
| `docs/research/v8-no-work-100-20260907/experiments/performance-svm/target/release/aspis-v7-pair-forest-combined-rejection` | 8873912 | `b12a43b4b27fa1b53b397e24a13ba4cbc6da218040a619e027fa4a5326b4e505` |

Host Rust1.94.1; SBF platform-tools1.54 / Rust1.89dev; Solana CLI2.3.0; Python3.12 / solders0.27.1. Optimized offline cached builds ran on the authorized dombarker NUC in individual systemd scopes: MemoryHigh5G, MemoryMax7G, MemorySwapMax0, two build jobs. Resource/exit logs are retained in `evidence/`; no formal replay was needed.

## Network and initialization

Read-only public and Helius RPC gates confirmed devnet genesis `EtWTRABZaYq6iMfeYKouRu166VU2xqa1wcaWoxPkrZBG`. TxV1 feature `txv1aq4pp281K9um3tnPgkfX8UqtFT6wcVW3hNezGLL` was active from slot492480000. Observed getVersion was4.3.0-beta.3 with feature set2409014235; response contexts also reported4.3.0-alpha.2. Exact responses are preserved. The confirmed transaction is version1,845 wire bytes,256KiB heap,8MiB loaded-account allowance and a10,000-lamport flat priority fee.

Local LiteSVM account injection is confined to the local fixture. Live state used supported System/SPL/Pool/Registry instructions: fresh mint and token accounts,13 fixed deposits across8 lanes, strict AS8V receipts and AS8K checkpoint, independently validated canonical trees. Proof create/write/seal/close was preflighted, including rejection of writes after seal and actual rent refund. Registry schedule/activation respected its delay and was frozen before the authoritative context snapshot at slot495742880. Verifier/proof identities were fixed before compilation/proving.

The unchanged Pool and Registry programs from the preceding isolated experiment were reused with entirely fresh settlement state and Registry entry. Neither was upgraded. This saves2.733370200SOL of duplicate Pool rent; the initially generated unused Pool key is retained. No production/shared deployment or other agents' worktree was changed.

| Public identity | Address |
|---|---|
| Fresh verifier | `C7S2E9cxTf7ff93DNYtoDE1CTrEQUx9T9JNF84R4YTfv` |
| Verifier ProgramData | `9tGewwo9fbWsVLGy4KiNGvvmmKcoJah6DGoMBUfwW8Dc` |
| Retained isolated Pool | `CWc8x6vhwX5UUUwNE6ys5vjT5vPUYahHu1JmEG8DtJMr` |
| Retained isolated Registry program | `5t5jGysv18VHEHrjhoTKeV3n1Jw7cfDqmMvadxU2UiQV` |
| Fresh mint | `FKM1Ahzp5c5s6L2sNmPAZmAVGHoAhAhuK1EdKxJPEPgQ` |
| Fresh source token account | `AurRHULawQ28trTDoU4NCg2QuFzWuhodmVr2serhv8at` |
| Fresh proof account | `7HHWUEYKhfR4wJGT9ESNbEkKya3dUK6LdYTEy8zKt6nW` |
| Fresh malformed proof account | `4fQHbG5jF34rVGSpg5J9xhbwh67kNEQke2WDzTf4swti` |
| Fresh master | `GfjobTU3uYNufSFGgYZZ4sv7f2Reie1FGXzM6aF6MnfZ` |
| Fresh checkpoint | `ZN6FM4h55NjLD9sSEGikrvxnpxn88294kEqgncxcomy` |
| Output lane3 | `7LTrsyaxmvtnECAzgm23hK9gndNSxEJetBLLzTcsjPX4` |
| Current history page | `ASHaqJVHngr4NvbaawePAnCBCa9uooygBXRBnnMtMXH8` |
| Consumed nullifier marker | `3o5mHiqv8tjejDAFmZvHaEBDPzXTkETSAy2VQEZgffbj` |
| Retained payer | `FrxmxTHqFqqqRj1MQB4FKNx8Bg4eCiHwqVNDbgwPuBu4` |

Complete account IDs/instruction encodings are in `identities.json`, `plan.json`, `registry-plan.json`. Every confirmed harness signature and devnet explorer link is indexed in `evidence/live/live-summary.json`, with raw receipts per phase. Loader deployment receipts are separate; only the new verifier was deployed in this run.

## Proof, settlement and controls

The fixed-seed1 genuine prover took3.129933613s excluding1.321557980s setup; process wall4.48s, peak RSS203,076KiB, swap0, exit0. Body39,294bytes + candidate688 =39,982 uploaded bytes; account header40 yields40,022 account bytes. Proof-body SHA256: `e20f95ceaa740bb8a9bcc478e466b080c43abade8c1576ff85926a9a48a07bb9`. Authoritative statement1880bytes SHA256: `0cc3e07ef0cee1597da9b498bb5b0393f1ffe73e9e0e5216eafc047fafa11fee`. Compiler transition and proof/statement/candidate binding checks passed before submission.

Before snapshot495744974; after495745025. Output lane sequence1→2, with full lane/frontier and current-history-page bytes equal to the independently expected transition. Root changed from `2d576b23b0ea731d2f0d105962d2bb50f51be95a3230ad2367d69257c8be6c5a` to `886282460b1ee85ff7518005f89d69503470ed628255915623182270de3fe454`. The exact208-byte nullifier marker was created with1,706,880lamports. Returned statement matched exactly. Other7 lanes, master, checkpoint, Registry/entry, mint, source and vault were unchanged. Mint supply13,000, source0 and vault13,000 are unchanged because this transfers private notes. The proof remains sealed/read-only; nullifier state enforces consumption. Payer decreased by exactly1,721,880lamports: marker rent plus15,000 fee.

| Control / transaction | Local full transaction CU | Devnet CU | Result |
|---|---:|---:|---|
| Genuine1000→600+400 | 1,150,565 | 1,105,880 | Complete settlement passed |
| Recipient zero | 519,470 | 479,181 | Semantic Custom4; settlement unchanged |
| Change zero | 519,472 | 479,174 | Semantic Custom4; settlement unchanged |
| Noncanonical first M31 limb | — | 91,697 | Custom3; settlement unchanged |
| Replay | — | 28,846 | Custom0x41532026; settlement unchanged |

Negative settlement calls were exact signed RPC simulations, not submitted failures. Their account lifecycle transactions were confirmed. The two zero-output bodies have genuine C1/C2 commitments and ten semantic rounds but deliberately unconstructed later PCS suffixes. These are bounded checks of the repaired semantic rejection boundary, not complete accepting adversarial proofs or a universal soundness theorem. Each zero-control proof account refunded130,789,680lamports by supported close; malformed proof rent was also reclaimed. Exact before/after images and raw errors are retained.

## Costs and differences

Atomic settlement fee15,000lamports, declared1.2M CU, confirmed1,105,880CU. Verifier CPI alone consumed1,049,083CU; the reported headline includes Pool settlement overhead. Setup and upload are separate:

| Confirmed harness group | Transactions | Fees (lamports) | Total wire bytes |
|---|---:|---:|---:|
| atomic_settlement | 1 | 15000 | 845 |
| zero_output_control_lifecycle | 26 | 530000 | 60018 |
| pool_registry_setup | 23 | 415000 | 12431 |
| funding | 1 | 20000 | 304 |
| genuine_proof_lifecycle | 17 | 345000 | 45785 |
| lifecycle_preflight | 4 | 85000 | 1464 |
| malformed_control_lifecycle | 18 | 365000 | 46078 |
| program_upload | 269 | 4040000 | 1039838 |

Native loader CLI deployment is additionally recorded in its raw receipt; the table counts TxV1 harness receipts only. The genuine proof lifecycle is17 transactions, including15 upload writes, create/init and seal. New verifier account+ProgramData rent is4.890256920SOL. RegistryV2 requires an immutable verifier: authority was removed only after local and live setup/lifecycle gates, making that loader rent irrecoverable. Pool authority and every wallet key remain retained.

This run recovered6SOL from the authorized dedicated Colosseum regime devnet wallet, retaining1.896892640SOL there. Cumulative external funding is24SOL within the25SOL authorization. Final payer balance is **1.355749028SOL**, finalized at slot495745264. No other-repository game/program account was closed. The preceding demo's settlement accounts remain byte-identical excluding the shared payer (`prior-demo-preservation-final.json`). All submitted harness receipts are reconciled.

Compared with the preceding selected-profile live result1,083,081CU, the repair costs22,799CU more (about2.1%). Different profile/transcript/identities/state prevent attributing that entire delta to one equation. The previous proof body was39,502bytes; this fixed transcript produces39,294, without searching. Final local1,150,565 versus live1,105,880 is also not an identical fixture/context comparison and is not claimed as a runtime speedup.

Preserved failures include the initial host-only mask helper SBF compile error (fixed cfg separation), the local diagnostic1.4M override dropping the requested heap (fixed driver default to the actual1.2M configuration), and refusal to overwrite existing fixture sidecars (archived before retry). No verifier check was weakened. Both initial and final identity local results are retained; final artifact and live context are pinned in `evidence/validation-pins.json`.

Reproducible ordered commands and safeguards are in [README.md](README.md), `run_local_nuc.sh`, `run_live_prover_nuc.sh` and the scoped deployment/lifecycle scripts. Private keys, synthetic witness material and credential-bearing RPC configuration stay outside Git. Important local, live-control and final-transfer milestones were sent through the repository Pushover helper.
