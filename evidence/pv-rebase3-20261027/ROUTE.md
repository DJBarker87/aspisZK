# Selected proof-account client route

Build source: `37794d7bff003fe396b43eb6e264bd9b29f40575` (merge plus the previously audited standalone lock repair). Rustc 1.94.1, release, offline, locked, `-j 4`, `r1p-check,aspis-r1-cost-probe/ct-host-prover`, `RUSTFLAGS=-C link-arg=-Wl,--threads=4`. No `optimized-terminal` feature in this client recipe.

Actual `devnet_spend`: SHA-256 `9ac299ded6ef01aa4fa16d6ff3ad20a74c3e816c88040b5f9b5fdb57fc9c4d84`, 2,744,920 bytes. Build, toolchain, resource and binary receipts are in `candidate/build-devnet/`; static extraction receipts are in `candidate/binary-route-audit/` and `binary-route/`.

| Resolved caller | Machine call site | Resolved callee |
|---|---|---|
| `devnet_spend::main` (`0x99310`) | `0x99435` | `devnet_spend::plan::run` (`0x7d1e0`) |
| `devnet_spend::plan::run` | `0x7d7fd` | `devnet_spend::plan::prove` (`0x85700`) |
| `devnet_spend::plan::prove` | `0x88e07` | `aspis_r1_cost_probe::prover::retry_attempt` (`0x97a90`) |
| `retry_attempt` | `0x97b13`, RIP-relative GOT slot `0x225990` | `StateOnlyAttemptSecrets::generate_for_mask_nonce` (`0x13fdd0`) |

`RealR1_client::prove_for_proof_accounts` and the generic retry owner are inlined into this specialization: neither has a standalone named symbol in this binary. The source binding supplies those inlined edges: `plan.rs:116` calls the adapter, `RealR1_client.rs:27` calls `prove_masked_retrying_with`, and its callback at line 28 calls `generate_for_mask_nonce(proof_account(k))`. The resolved machine path reaches that selected64 generator. No generic96 generator is reachable in the resolved graph. `route-symbols.json` records the instructions, addresses and relocation resolution; the full symbols/disassembly/relocations remain retained on the host and are hashed in `meta.json`.

`source-route.json` lists the complete pinned operational/source chain and actual line numbers. Six planner/account/adapter/operational files byte-equal the D162 client pin `5228877938`; the entropy file deliberately retains the candidate D187 rewrite, byte-identical to pre-merge candidate. It accepts the public proof-account nonce and requests a 64-byte OS fill, split into field and leaf seeds. This is source/binary reachability evidence, not a formal source-to-machine refinement, entropy-law proof, complete taint graph, timing result or side-channel theorem. Register-indirect/dynamic edges outside this resolved path retain the extraction's stated limitations.

The account policy uses eight retained, distinct, canonical nonzero public keys; callback order is checked; successful `attempts - 1` selects the same account for stage1 publication and settlement. No operational client, signing, RPC, funding or deployment run was performed in this task. The deterministic fixture gate uses the unchanged example directly, separately from this static client binding.
