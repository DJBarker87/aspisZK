# Proving-client source revision for the NDZ (2026-10-29) and NPC_ (2026-11-10) devnet runs

Read-only fact-finding. No git state was changed and nothing was run on the build host. Paths are relative to /Users/dominic/ZK.

## Short answer

Both devnet runs proved with one client binary. It is `devnet_spend`, SHA256 77e7e541378baa655ba8ebd47052e67a145807392e03d7ce48d6a4bb13ca8289, at /opt/aspis/devnet_spend inside the Mac Docker image sha256:a5fd19592cef47ad41bf1891997e324febf21a442cc71fac4eaf77877d60562a. The evidence attributes it to the revision **dfa35acd8390aea176c13710d320d041332b320a** (2026-10-29, "Devnet: July legacy program closed..."), not to 4bb3b3f.

At dfa35acd, these paths have git tree hashes identical to 4bb3b3f: `crates/` (all of aspis-core, aspis-prover, aspis-statement and aspis-r1-cost-probe), `programs/aspis-registry`, root Cargo.lock, `tools/r1-cost-probe/Cargo.lock` and the z4 probe crate. The binary's own crate, `tools/r1-cost-probe`, differs from 4bb3b3f. Two things the binary links are outside the D1084 pin as written:

- the tool crate, at its dfa35acd/HEAD tree rather than its 4bb3b3f tree;
- the 4bb3b3f/dfa35acd Pool source as a library. This is not b936275's Pool.

Both devnet runs generated their proofs fresh at run time. They were not reused fixtures. The link from the binary hash back to a source tree rests on worker-written statements, not on a recorded hash chain.

## (a) What the client was built from

- Build command: `cargo build --manifest-path NDZ_src/tools/r1-cost-probe/Cargo.toml --release --locked --offline -j 4 --features r1p-check --bin devnet_spend`. Exit 0, wall time 1:13.74, max RSS 485504 KiB, cgroup 4G/6G with swap 0 (evidence/devnet-rehearse-20261029/NDZ_client-build4.time, NDZ_PROCEDURE.md:24-32). Host root: /home/dombarker/project-offloads/codex-cx-devnet-rehearse-20261029/NDZ_src.
- Source: NDZ_PROCEDURE.md:12-15 says "The native selected64 client is built from the inspection revision" dfa35acd. NDZ_STAGE0.md:4 says the same. Every host receipt records `source_revision: dfa35acd...` and `frozen_revision: 4bb3b3f...` (NDZ_spend-receipt.json, NDZ_final_spend-receipt.json). NPC's local receipt records `client_source_revision: dfa35acd...` (devnet-frozen-20261109/local/out/NPC_spend-receipt.json).
- Crates compiled in build 4 (NDZ_client-build4.log): aspis-pool (programs/aspis-pool), aspis-prover, aspis-r1-cost-probe, aspis-r1-cu-probe (tools/r1-cost-probe, which contains the devnet_spend binary), aspis-registry, aspis-statement, and aspis-z4b-probe (docs/research/v8-r0-zk-20261009/z4). aspis-core was already fresh from earlier preflights, and its warnings point at NDZ_src/crates/aspis-core.
- Workspace and lock: tools/r1-cost-probe/Cargo.toml has its own `[workspace]`, so `--locked` used tools/r1-cost-probe/Cargo.lock. Its git blob is a056d6f8 and its SHA256 is 08de51ef...57b3f9. Root Cargo.lock has SHA256 5782e6a3...ba22ef, the value NPC records for the verifier build.
- Features in the binary (tools/r1-cost-probe/Cargo.toml at dfa35acd):
  - aspis-prover with features `r0` and **`insecure-spend-fixture`**;
  - aspis-r1-cost-probe with `prover`, `r1p-check` and `private-leaf-salts`;
  - aspis-statement with `r0` and `pool-v1-kernel`;
  - aspis-pool with `no-entrypoint`, `pair-forest-account-evidence` and `pair-forest-verifier-lane-invariant-audit`;
  - aspis-registry with `no-entrypoint`.
- Image recipe: evidence/devnet-rehearse-20261029/NDZ_writer.Dockerfile (ubuntu:24.04@sha256:fe815609..., apt python3/ca-certificates/libudev1/libcap2, `COPY cli /opt/aspis/cli`, `COPY devnet_spend /opt/aspis/devnet_spend`). Build log: NDZ_writer-build.log.gz, with a 41.61 MB context. In-image hashes are in NDZ_WRITER_READINESS.json runtime_checks: devnet_spend 77e7e541, solana b6134ccd, solana-keygen c3385c5a.
- No toolchain is recorded. The build log and receipts give no rustc/cargo version, only /home/dombarker/.cargo/bin/cargo.

## (b) Byte identity against 4bb3b3f (git rev-parse <rev>:<path>)

| Path | 4bb3b3f | dfa35acd (client) | HEAD | b936275 (Pool pin) |
| --- | --- | --- | --- | --- |
| crates | 9c52e6b9 | same | same | same |
| crates/aspis-prover | c885d9b0 | same | same | same |
| crates/aspis-statement | e42a9192 | same | same | same |
| crates/aspis-core | 0fff78ef | same | same | same |
| crates/aspis-r1-cost-probe | 8415f53a | same | same | same |
| programs/aspis-registry | 71206322 | same | same | same |
| programs/aspis-pool | 480e2c48 | same | **bf9ea55d** | **bf9ea55d** |
| docs/research/v8-r0-zk-20261009/z4 | 21cf8e2a | same | same | same |
| Cargo.lock (root) | 8b19d7e9 | same | same | same |
| tools/r1-cost-probe/Cargo.lock | a056d6f8 | same | same | same |
| **tools/r1-cost-probe** | **32981bc2** | **82699657** | 82699657 | 82699657 |

The tool crate differs from 4bb3b3f in three files, with 1031 lines added and 5 removed:

- `src/bin/devnet_spend/Client64_accounts.rs` is new;
- `src/bin/devnet_spend/plan.rs` changes the prove call;
- `src/bin/pv_client_gate.rs` is new.

The commits are b7cd400a556, 5270ce4bf3a, 7c63aed20f0, 6a1a7ce4144 and ce5583a4a20.

The plan.rs change matters. 4bb3b3f's client calls `prover::prove_masked_retrying(..., Variant::S2, HOST_HASH, &mut store)`. The devnet client calls `RealR1_client::prove_for_proof_accounts(..., HOST_HASH, &mut store, |k| accounts.nonce(k))`. That function is in the unchanged crates/aspis-r1-cost-probe/src/RealR1_client.rs:20. It derives each attempt's mask nonce from the selected proof-account key and draws the two 32-byte seeds from the OS. The prover library is the frozen one, but the entry point and the per-attempt nonce source are those of dfa35acd's tool crate.

The NDZ branch commits after dfa35acd (6bffd9f3f05..476545f9ce2) change only scripts and evidence. tools/r1-cost-probe and crates keep the same trees, so no later tool change entered the binary.

## (c) Run-time proofs or fixtures

- NDZ devnet, 2026-10-29: fresh. evidence/devnet-rehearse-20261029/NDZ_devnet_receipts/NDZ_spend/transfer-proof-plan.json and withdrawal-proof-plan.json show prove_wall_seconds 43.08 and 39.98, attempts 1, client_route selected64-proof-account-v1, and proof_bytes 58295. NDZ_devnet.review-only.json sets signer /opt/aspis/devnet_spend and has no proof_cache_reuse. NDZ_PROOF_REUSE.json covers only the *local* final rehearsal, which reused proofs from the first local run (NDZ_spend). It does not apply to the devnet run.
- NPC_ devnet, 2026-11-10: fresh. devnet-frozen-20261109/devnet/NPC_devnet_receipts/NPC_spend_receipts.tar.xz has NPC_spend/{transfer,withdrawal}-proof-plan.json with prove_wall_seconds 43.12 and 38.33 and attempts 1. NPC_devnet.json sets signer /opt/aspis/devnet_spend, has no proof_cache_reuse, and runs through NPC_writer.sh with the same image a5fd1959.
- NPC_ local: fresh (`proof_cache_reuse: False`, NPC_prepare_local.py:18). It used the host binary NDZ_native-target/release/devnet_spend, not the image.
- The witnesses are public deterministic fixtures in all runs: notes and salts are derived from `digest(seed)` in plan.rs, and complete.json has `fixture_witnesses_public: true`. Only the proof randomness is fresh.

## (d) Gaps

1. **The pin and the client source differ.** D1084 records the pin as "crates, programs/r1-cost-probe and Cargo.lock at 4bb3b3f51e1 with programs/aspis-pool at b936275465". The binary that ran was built from tools/r1-cost-probe at dfa35acd, a different tree from 4bb3b3f (above). That tree is unchanged at HEAD and b936275. It also links `aspis_pool::*`, and uses it for instruction encoding and PDA and marker derivation, from the 4bb3b3f/dfa35acd Pool tree 480e2c48. b936275's Pool tree is bf9ea55d: 15 files, 268 lines added and 13336 removed against 4bb3b3f. On NPC devnet, a client built against the older Pool library drove the b936275 Pool ELF e0e49c34. For the single model to equal the devnet code, the pin must name tools/r1-cost-probe at dfa35acd (tree 82699657) and state which Pool tree the client links.
2. **The source tree has no hash chain to the binary.**
   - NDZ_src was an archive, presumably of dfa35acd, and four preflights "repaired missing archived path-dependency/include files" (NDZ_PROCEDURE.md:26-28). No file list or tree hash of NDZ_src was recorded.
   - The receipts' `source_revision` is a hard-coded string in NDZ_run.py and NPC_local_run.py, not a measured value.
   - No host-side SHA256 of NDZ_native-target/release/devnet_spend was recorded. Nothing ties the image's COPY source to the host build, beyond the workers' prose that it is "the exact rehearsed Linux client".
   - NPC_LOCAL_RESULT.md:20 calls the host binary 77e7e541, but its receipt does not hash it.
   - The rustc version is not recorded.
   - No reproducible rebuild has shown that dfa35acd plus the recorded command gives 77e7e541.
3. **The binary has the `insecure-spend-fixture` feature enabled** on aspis-prover. crates/aspis-prover/Cargo.toml says this feature is "intentionally not enabled by any production crate" and that it "exposes fixed attempt entropy". The devnet prove path reads OS seeds through RealR1_client and does not appear to call the fixture entropy. Still, any model extracted from the pin must use the same feature set as the binary, or justify the difference.
4. **The binary was run under emulation.** It is linux/amd64 and ran under Docker emulation on the Mac for both devnet runs. The NDZ local and NPC local runs used the host build. The two are the same binary only if gap 2 is closed.

## What would close this

- Rebuild dfa35acd:tools/r1-cost-probe with the recorded command and features under a recorded toolchain, then compare the result with 77e7e541. Either reuse the image's binary or extract it with `docker cp`, read-only.
- Record the source tree hash used.
- Amend the D1084 pin to include tools/r1-cost-probe at dfa35acd and the client's linked Pool tree, and state the feature set.

Target not yet established.
