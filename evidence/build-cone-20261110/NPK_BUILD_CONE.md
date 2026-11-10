# NPK_ build cone of the deployed verifier and Pool ELFs

Job NPK_, Stream A, 2026-11-10. Branch codex/cx-cone-20261110. Target not yet established.

## What this packet establishes

It gives the exact list of in-repository source files that the compiler opened while building the
deployed verifier and Pool ELFs. Each list was taken from builds that reproduced the pinned bytes.
It also gives the list of files that the frozen-tree Charon extraction configurations open on the
host target. It names the files in those lists that also contain prover-gated code, and the
prover-only files outside both lists. These lists are the inputs for gate items (2) and (3) of a
prover-only refactor.

It does not establish that any refactor is admissible. It does not run Charon or Aeneas, so gate
(3) "the emissions regenerate identically" is not exercised here. Only the file inputs of that gate
are listed. Nothing in the source, the ledger, any trust row or the security contract was changed.

## Method

1. Source exports, built on the NUC in /home/dombarker/project-offloads/codex-cx-cone-20261110.
   `src-v` is `git archive 4bb3b3f` over the NOX input set: Cargo.toml, Cargo.lock, .cargo,
   crates, programs, xtask, audit/poseidon-pair-probe/program, and docs/research/v8-r0-zk-20261009/
   {refine/writers, refine/blockwriters, refine/poseidon, z4, c3}. It has 1,180 files, and
   `diff -r` against NOX's own tree (codex-cx-l188-20261109/src) is empty. The tar sha256 is
   65315e53…d5ad. It differs from NOX's 40494a95 only in tar metadata, because the file contents
   are identical. `src-p` is the same export of b936275 (1,172 files, tar 3bc02899…f86e).
2. Builds (receipts in host/receipts/, scripts in host/NPK_build.sh and host/NPK_scope.sh). Each
   build used the NOX_B002/B003 recipe: cargo-build-sbf 3.1.13 (sha256 46e50d5d…5d6c),
   `--skip-tools-install --offline -j 4 -- --locked -v`, and `env -i` with HOME, USER,
   `PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin`, CARGO_HOME, a fresh kept CARGO_TARGET_DIR,
   `CARGO_NET_OFFLINE=true` and `CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS=-C link-arg=--threads=4`.
   There was no RUSTC_WRAPPER and no CARGO_PROFILE_RELEASE_BUILD_OVERRIDE_OPT_LEVEL, and CPU
   affinity was taskset 0-3. A directory placeholder at the keypair path suppressed key
   generation, as in NKX, so no key was created or read. The verifier used
   `--features pool-adapter,private-leaf-salts`. Devnet added the NOX Pool and registry IDs, and
   retarget added the NPC Pool ID 37hdATMk… with the same registry ID. The Pool used
   `--features r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit`
   (the NKX pool1 features, here under the NOX env -i shape and without the NKX diagnostics wrapper).
3. Cone extraction (host/NPK_collect.py). Every `.d` dep-info file in the kept target directory
   was parsed: `sbpf-solana-solana/release/deps`, the host `release/deps`, and the build-script
   units. A path is in-repository when it is relative to the workspace root or lies under the
   source export. The `-v` rustc command lines give the `--cfg feature=` set of every unit.
   Dep-info lists every file that rustc opened, including `include!`/`include_str!` targets and
   build.rs.
4. Pin check (NPK_analyze.py). The sha256 of every cone file on the host was compared with the git
   blob at the pin: 4bb3b3f for the verifier and the extraction cones, b936275 for the Pool.
   There were 0 mismatches.
5. Extraction cones (host/NPK_native.sh). `cargo check --release --lib --locked --offline` ran on
   the host target with the Charon driver's toolchain (nightly-2026-06-01). It ran over the NHR
   staged extraction tree: the 658 files of PCO_E001/sources/NHR_STAGING_MANIFEST.json, written
   from their git blob ids and sha256-checked. Five configurations were run, which are all the
   frozen-tree configurations used by the 241 committed `prov-p*/…_spec.json` files on research.
   A sixth run (N016, `prover,r1p-check`) gives the prover cone. `cargo check` dep-info is
   front-end dep-info: the same files are opened as in Charon's `--mir built` front end. This
   is the method's assumption. Charon itself was not run.
6. Prover cfg scan (NPK_cfgscan.py). Every cone `.rs` file was scanned for `#[cfg(..)]`,
   `#![cfg(..)]`, `#[cfg_attr(..)]` and `cfg!(..)` whose predicate names `prover` or `r1p-check`
   (r1p-check implies prover). The scanner computes the item extent and evaluates the predicate
   under the deployed feature set with and without the prover features. The scanner is
   heuristic. Its ranges were spot-checked by hand (r1_semantic.rs 95-229) and should be re-read
   before an edit.
7. `cargo tree -e normal --target sbpf-solana-solana` and `-e normal,build` ran with the
   platform-tools cargo and the deployed features (host/out/NPK_T001). Their per-crate features
   agree with the rustc `--cfg` lines. `cargo metadata` resolves the whole workspace and lists
   features that are not compiled into the programs (for example aspis-statement
   `spend-dynamic-rate512`). It is kept compressed for reference, but it is not the authority for
   build features.

## Builds: all four ELFs reproduced

| Attempt | ELF | sha256 | Bytes | Wall | Peak RSS (KiB) | cgroup peak | Swap | Memory events |
|---|---|---|---|---|---|---|---|---|
| NPK_B001 | verifier default | f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4 (identical) | 1,563,728 | 69.2 s | 647,272 | 1,596,325,888 | 0 | none |
| NPK_B003 | verifier devnet | 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299 (identical) | 1,563,728 | 67.8 s | 647,172 | 1,249,386,496 | 0 | none |
| NPK_B004 | verifier retarget (NPC) | 2331ad8a2d97439a30329328c51f619a6b13be97e260ab1e1fd8aab22cb996ea (identical) | 1,563,728 | 75.6 s | 647,020 | 1,260,929,024 | 0 | none |
| NPK_B002 | Pool | e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc (identical) | 345,648 | 78.4 s | 643,704 | 1,187,885,056 | 0 | none |

Caps for every scope: MemoryHigh 6G, MemoryMax 8G, MemorySwapMax 0, TasksMax 64, and a 1800 s
timeout for the build class. Admission required at most 3 other user scopes, at least 56 GB free
disk, and a reservation scan with allowed = true. Cargo.lock was unchanged before and after every
build (5782e6a3…ba22ef). No Lean was run, so `#print axioms` is N/A.

## Resolved features (rustc `--cfg feature=` lines; cargo tree agrees)

| Crate | Verifier ELFs (all three) | Pool ELF |
|---|---|---|
| aspis_r1_cost_probe_program | custom-heap, default, pool-adapter, private-leaf-salts | not in cone |
| aspis_r1_cost_probe | default, optimized-terminal, private-leaf-salts, program-build. **`prover` is OFF** (also `r1p-check`, `audit-eight-way`, `detail-phases`, `r0-op-count`) | not in cone |
| aspis_statement | pool-v1-kernel, r0, and 12 pool-v1-pair-forest-*-audit features (the 9 named by optimized-terminal plus copy-pattern-basis, copy-selector-tensor-basis, packed-digest through feature implication) | pool-v1-kernel only |
| aspis_core | r0 | none |
| aspis_pool | not in cone | default, pair-forest-account-evidence, pair-forest-source-invariant-audit, pair-forest-source-result-invariant-audit, pair-forest-verifier-lane-invariant-audit, r1-split-checkpoint |

Dependencies not in either SBF cone include aspis-prover, aspis-pool-wallet-v1, aspis-z4b-probe
(z4), the c3 crates and the three writer-copy crates under docs/research/v8-r0-zk-20261009/refine.
The writer copies are `cfg(not(target_os = "solana"))` dependencies of aspis-statement, so they
are compiled for the host only. The three verifier builds compile the same 132 files with the same
`-C metadata` hashes. The devnet and retarget IDs enter only as `env-dep`s of
programs/r1-cost-probe/src/lib.rs (ASPIS_R1_POOL_PROGRAM_ID, ASPIS_R1_REGISTRY_PROGRAM_ID).

## Cone sizes

| Set | Files | Content |
|---|---|---|
| Verifier cone (B001 = B003 = B004) | 132 | aspis-core 66 (65 src + build.rs), aspis-statement 43, aspis-r1-cost-probe 17, programs/r1-cost-probe 5, and **programs/aspis-verifier/src/v7_pair_empty_roots.rs** (pulled in by `include!` from programs/r1-cost-probe/src) |
| Pool cone (B002) | 126 | aspis-core 66, aspis-statement 42, programs/aspis-pool 18 |
| Verifier and Pool shared | 108 | aspis-core 66 and aspis-statement 42 (everything except aspis-statement/src/r0.rs, which only the verifier compiles) |
| Extraction cone (host target, N011..N015) | 154 | 132 of these are in the verifier cone. **22 are in neither ELF cone**: 18 host-only aspis-statement modules, the 3 writer-copy `src/lib.rs` files, and docs/research/v8-r0-zk-20261009/refine/diffharness/tests/glue_gen.rs (`include!`d by pool_v1/pair_forest_copy_builder.rs on the host) |
| Gate union G (V ∪ P ∪ X) | 172 | table below |
| Generated input | 1 | OUT_DIR/circle_tables.rs from crates/aspis-core/build.rs, sha256 7fbe0464…6491, identical in all four ELF builds |

Build-selection inputs that are not in dep-info but determine the build also belong in the gate.
They are identical at 4bb3b3f and b936275: root Cargo.toml 3de458ef…, Cargo.lock 5782e6a3…,
.cargo/config.toml 0bd9c48d…, and crates/aspis-core/Cargo.toml, crates/aspis-statement/Cargo.toml,
crates/aspis-r1-cost-probe/Cargo.toml, programs/r1-cost-probe/Cargo.toml,
programs/aspis-pool/Cargo.toml, plus the three writer-copy Cargo.toml for the extraction (hashes
in NPK_CONE_FILES.json `manifests`). Root Cargo.toml carries `[workspace.package] version` and the
profiles. A crate's version and source path feed the `-C metadata` hash, and NOX showed that a
metadata change alone moves code in the ELF.

Tree hashes (identical at both pins except the Pool program): crates 9c52e6b9, crates/aspis-core
0fff78ef, crates/aspis-statement e42a9192, crates/aspis-r1-cost-probe 8415f53a, crates/aspis-prover
c885d9b0, programs/r1-cost-probe 7f2e497c, programs/aspis-pool 480e2c48 (4bb3b3f) / bf9ea55d
(b936275, the deployed Pool), refine/writers bc137c4b, refine/blockwriters f7ced3e4,
refine/poseidon b8729182, z4 21cf8e2a, Cargo.lock blob 8b19d7e9, Cargo.toml blob bdc6be47.

## Gate file list G (172 files; V = verifier ELFs, P = Pool ELF, X = extraction configurations)

The sha256 is the file content at the pin (4bb3b3f, or b936275 for programs/aspis-pool). "Path in
ELF" means that the relative path string occurs in the stripped ELF. These are panic and
bounds-check `Location` records, which carry the line and column.

| path | sha256 | V | P | X | path in ELF |
|---|---|---|---|---|---|
| crates/aspis-core/build.rs | `fe5aebdbcad65764c4eb34cee39fa60621e7bdfc6de262664990fe9ee1ef3edc` | V | P | X |  |
| crates/aspis-core/src/circle.rs | `8f6f0f32c8dd93e3ee459df0c1d0ef710b01996d3bc929dbeffb3f7d14a0227c` | V | P | X |  |
| crates/aspis-core/src/circle_fri.rs | `f883d298fb4790d3e69131b90d8626c5083ff194655522e3047f849138460dcc` | V | P | X |  |
| crates/aspis-core/src/circle_hiding_prefix.rs | `92f47e55f9d1e73280e48de7563e40685e88ff78c21f589fa98a4cc2c4c31973` | V | P | X |  |
| crates/aspis-core/src/circle_hiding_query.rs | `f256ea7b9ae761df4834aa902a250a539c06f5b23cdefab7cb7698eb51290029` | V | P | X |  |
| crates/aspis-core/src/circle_line_merkle.rs | `d226fd9b200ea829fca0fe8a045b9ede1408a2f0387db7916facc908544284a8` | V | P | X |  |
| crates/aspis-core/src/circle_merkle.rs | `826736d396946cf7927d4617dcd0e4706ab08c0d778b647117c7369ed9ab7592` | V | P | X |  |
| crates/aspis-core/src/circle_openings.rs | `8ad10e78495fa67924a38606cc8c7e8bd3e96741fa12bd6abe731c90a89d26f6` | V | P | X |  |
| crates/aspis-core/src/circle_pcs_shape.rs | `0de69556b718b8184f6c65f698b6ce7e4347c80f652bd4e1a84fa7e7809e5093` | V | P | X |  |
| crates/aspis-core/src/circle_prefix.rs | `437a5c853f8018ffa256cfa14a5f36e718cb2b1fc39410e82e9a0fc455a8c4db` | V | P | X |  |
| crates/aspis-core/src/circle_query.rs | `5da1dbee29f3a052ad260ebbaeda0233dadb9ed3cf6d04f2a5c2cf84352e31de` | V | P | X |  |
| crates/aspis-core/src/digest.rs | `e9a3476d8d3f05639253ea663aebaade2318af60e2ea0fd87a280e058208aba0` | V | P | X |  |
| crates/aspis-core/src/field.rs | `28df5a1abee13bde4b3aa9eeceb0489bedf00531f298460954a97661f5f1baea` | V | P | X | yes |
| crates/aspis-core/src/field/wide_exact.rs | `6260fa9d179328714e7df59640abb7a76a326e98900993ce7d3da98c6411d10b` | V | P | X |  |
| crates/aspis-core/src/lib.rs | `c179731989675fa3218cf2230ec3681d2e61d23c2b2694ea10b72fb68ee377d0` | V | P | X |  |
| crates/aspis-core/src/merkle.rs | `88e5ff328069d4dc802203746de7123c1a150d0d7a49393a7a880d50e2d38a18` | V | P | X |  |
| crates/aspis-core/src/params.rs | `5f1e013c441f80b04c7960af8d4d3ae8ebbd295fe0031e9b60dd9e85b2be10b3` | V | P | X |  |
| crates/aspis-core/src/proof.rs | `a8e3b259da25d47a3d88b38ca838d57ab104476929fe5758b43d1a37c06306a0` | V | P | X |  |
| crates/aspis-core/src/r0/basis.rs | `f557751312781a0dec538b9b3934436e20644f4430144c5a612cfe6bc8d06166` | V | P | X |  |
| crates/aspis-core/src/r0/chord.rs | `b3a3d096fec5f307613ad87525eea452bae5c13080a7f52816e0dc0b986f1868` | V | P | X |  |
| crates/aspis-core/src/r0/domain.rs | `43bfef6f29698a4751504f9adee0e7dfdd092f6ecae6ace16f498cb2ef0fe068` | V | P | X |  |
| crates/aspis-core/src/r0/encoder.rs | `6e34b6b2b264573e63f963fe2879d05eaed4f767e105bf7ca0c79d5b6dfc5c88` | V | P | X |  |
| crates/aspis-core/src/r0/fold.rs | `06afbfb2c1c03306b59136695fdbf89382e21ed420f123982a70e977c2f35e39` | V | P | X |  |
| crates/aspis-core/src/r0/heap.rs | `67153a3fb69c839160855a9b8fdb886fbd1eac90f4dc686260f23a85e346e4f9` | V | P | X |  |
| crates/aspis-core/src/r0/merkle.rs | `ad0f32108562607b9454ac911471a8bebe6306ce98c69eed742c8f8f3985c554` | V | P | X |  |
| crates/aspis-core/src/r0/mod.rs | `709f1d0d9be9d3ee74e2b63e13065f5a91c878ba77ed2d2e97a414fbbc646aca` | V | P | X |  |
| crates/aspis-core/src/r0/onchain.rs | `08468c643f1b909ee811984cf7a2dde1d9fb1e6c8dd9c943d5904fcf0f493421` | V | P | X |  |
| crates/aspis-core/src/r0/opening.rs | `349dc999c1165e9e3be07a840ce99dc7a0b567c7a0545088baea80894476ee7d` | V | P | X |  |
| crates/aspis-core/src/r0/prover.rs | `4d4d8634bcb872d372bd430ac56cd60aece6d60e87e505126ce9ab46d2ef6c28` | V | P | X |  |
| crates/aspis-core/src/r0/scalar.rs | `a36f076d3333ad53e01815bda7d030ce12e9c6e30aafc475d928d4df8af11d44` | V | P | X |  |
| crates/aspis-core/src/r0/structured.rs | `c5eb9569c3819e95ccd55e87b7c888f367b433c8a63c4ea7ab4c34389a1d3f74` | V | P | X |  |
| crates/aspis-core/src/r0/top_overflow.rs | `d69cb3545a5cb93d5faaf005298459b3fe10f704ee82da7d97306cfc067cd89e` | V | P | X |  |
| crates/aspis-core/src/r0/transcript.rs | `0871a78b1c20a2b1dd2108dedf5865200a9213f6c2b5633cd920303f631bb623` | V | P | X |  |
| crates/aspis-core/src/r0/transport.rs | `ac892fa35fd6a8d697805770ece27fde79d1b91db619323870dff603b4f3045d` | V | P | X |  |
| crates/aspis-core/src/r0/transport_pads.rs | `f2b42975f868d78bb8ece807bf32f1c5e162f07521f5ec2c6f87f00df82a814c` | V | P | X |  |
| crates/aspis-core/src/r0/verifier.rs | `d8f06728e85236520d0d0f4c81fb5f24c31c5cf10a3bacf5bf1591d9a6631607` | V | P | X |  |
| crates/aspis-core/src/r0/wire.rs | `1e4910a77ddc0734967554c86266fb37496723a3c8eeb0b1fa9eaa12d4ea35bc` | V | P | X |  |
| crates/aspis-core/src/r0_transcript.rs | `2a315219d20069742c7c07e2a1ab8ee283865be3c607fdde2cf6975ad1813fc1` | V | P | X | yes |
| crates/aspis-core/src/state_only_hiding.rs | `cc1039531cfe07518542d386668e9572e3eacf5127e8ec441c32bec20d116cd2` | V | P | X | yes |
| crates/aspis-core/src/state_only_masked_switch.rs | `8704f8a9a23787ef468dbff013fb4211bda637d1ebd42908292c2a055b3f3c1d` | V | P | X |  |
| crates/aspis-core/src/state_only_masked_switch_basis.rs | `ec0a3646cf610b593b75179b751f27386f66903483227bbe14678ad0b3ab05ec` | V | P | X |  |
| crates/aspis-core/src/state_only_prefix.rs | `31c2cd269efadc9b41d77bb841c7728e11e7494b443dbfea4b1e804795c11d0f` | V | P | X |  |
| crates/aspis-core/src/state_only_private_merkle.rs | `6f9f030ea3add192358330f8012c81884a1f599e7dcd6b95ca837a5584ecd451` | V | P | X |  |
| crates/aspis-core/src/state_only_private_openings.rs | `75fae54796b9be405cfdf37e950bdb1b4b53da0cf447762635a4227d67cc0343` | V | P | X |  |
| crates/aspis-core/src/state_only_query.rs | `4e91b9b356998cc52f5482bc18c5de79b6dddeb9f9bb77bbf6af7d30ff401bd6` | V | P | X |  |
| crates/aspis-core/src/state_only_relation.rs | `e9e57e1497eceb22163698b466d059e14e76cff9ff998bf257d5bbd9533342eb` | V | P | X |  |
| crates/aspis-core/src/state_only_spend_openings.rs | `0e3de4cfb3678137b6260daec537e4d70b0c4d26e03a5ee3b99acad31a6c3681` | V | P | X |  |
| crates/aspis-core/src/state_only_spend_query.rs | `03d959ba62591dfdd55173a45e55647f38d9a0f1aded7dae1f654913aca2f0ac` | V | P | X |  |
| crates/aspis-core/src/state_only_spend_relation.rs | `6c82101c3546c2a26201731567aa687c6a9050b55bc0d88ac127131b5d9ba1dd` | V | P | X |  |
| crates/aspis-core/src/state_only_sumcheck.rs | `e09008daaaea9f35e2a28b85ec06f38dba75dbc9e6741d53a13020123f00d78d` | V | P | X |  |
| crates/aspis-core/src/statement_hiding.rs | `78b84cb12067d6f6f31068dd15aa76f4e9ecdb38315030d686040472814b1b9f` | V | P | X |  |
| crates/aspis-core/src/statement_sumcheck.rs | `f707317329a8e13bac2538d718b16e048bc58c7de82ef2bb08f0e0d75da66a78` | V | P | X |  |
| crates/aspis-core/src/sumcheck.rs | `7e12acf033a9c309a836dcb1c334c69932e15b97407613b3968f8e1c53787ead` | V | P | X |  |
| crates/aspis-core/src/transcript.rs | `9bd74c66a28567e4d964896b7e2d7c0ac79840565d44b561747879868bdd9179` | V | P | X |  |
| crates/aspis-core/src/v6_onefold.rs | `fa7977f2be11f4676146b802e687844086f0f33c56857c83514e8b6346f14fea` | V | P | X |  |
| crates/aspis-core/src/v6_query_batch.rs | `3c1d1dcdb2dcc9df30bf8723d9ba10444cbcd79bcbbca6854e1443eb1921eb9d` | V | P | X |  |
| crates/aspis-core/src/v6_transcript.rs | `48275a37053ce5d33c7ec61caf6301863666f45a1e388c2c64bdb856708764cf` | V | P | X |  |
| crates/aspis-core/src/v7_code_switch.rs | `4704d1e633b9c962f000246203caacb71928a06b24e2468a801489d60b940761` | V | P | X |  |
| crates/aspis-core/src/v7_compact_onefold.rs | `10527392130f25fd477084fd19da433c20f8bad45adc4f825b193e21b35ca765` | V | P | X |  |
| crates/aspis-core/src/v7_lane_zeta.rs | `41d0ad3a95b4d39d6ea39d67e81a2631dc138ebe8630c1a9ff4c77fcd8a8f5a3` | V | P | X |  |
| crates/aspis-core/src/v7_merkle.rs | `ca11ccce5a2a0915ff8979a8ce275912eddbba9c696b770f438f2d957250ad95` | V | P | X |  |
| crates/aspis-core/src/v7_merkle208.rs | `071ade1236140fdae559bb7b607ac9b7ee299e74eccb16b3385e3b1bbf215fdf` | V | P | X |  |
| crates/aspis-core/src/v7_onefold.rs | `6abb0376100611c5553258062480777187785579f402c9c1d3ce72379518258f` | V | P | X |  |
| crates/aspis-core/src/v7_profile.rs | `0b5f15c358f9897d84dcb6377e3ea448e5ebceba0bca42660ad60996de3c4a02` | V | P | X |  |
| crates/aspis-core/src/v7_staged_pair.rs | `501474bad8d39074b0e595e0956690ea5b785b6e5b33d9a1b126707c33b809ed` | V | P | X |  |
| crates/aspis-core/src/verify.rs | `108021252ada329b627808c045509eb0678c720b7ed052060213af0763b40656` | V | P | X |  |
| crates/aspis-r1-cost-probe/src/candidate.rs | `5164975df10f79e9810f9321b8130a9865eb9bb9b6b9de7011f4359ece98c794` | V |  | X | yes |
| crates/aspis-r1-cost-probe/src/compact.rs | `adcd99bdedda8ecdb250fb810ad9bcd263ce80a2c6cb6e7d2d3777587dabb9b7` | V |  | X | yes |
| crates/aspis-r1-cost-probe/src/fast_domain.rs | `bf4b66a59f6a23d19adf6f0021dfa0b9ddb010d6611181d13374fec12c612151` | V |  | X |  |
| crates/aspis-r1-cost-probe/src/fast_dots.rs | `53fa714e84ded64b844061f4d1b66ad20ee1ba48c3873a73970f80ede8a0b602` | V |  | X | yes |
| crates/aspis-r1-cost-probe/src/fast_pairing.rs | `7f75b58bfcaf7f586acb0152671e42565a549a8ace2b90dab794533dcdb6335e` | V |  | X | yes |
| crates/aspis-r1-cost-probe/src/lib.rs | `b4dcf882810c757beb5eaa105c8320cd9ebb19ae184824277900d6ad2c62d6fd` | V |  | X |  |
| crates/aspis-r1-cost-probe/src/multiproof.rs | `4c7e15f34b2a7ffd22ae5e47c3c58517c7855011cc6054ba2562c0399eb16bb3` | V |  | X | yes |
| crates/aspis-r1-cost-probe/src/r1_semantic.rs | `c66eba53bc3cdf801466455089d7189c02a0bec858f407a5fc9db35d10b17013` | V |  | X | yes |
| crates/aspis-r1-cost-probe/src/r1_wire.rs | `7479389501c3d2510f639546e0d834dbc42e2bed33c6b5d38c89b8b6318ae3b8` | V |  | X | yes |
| crates/aspis-r1-cost-probe/src/sampler.rs | `d7bd77dd4956e262cc21c381ec7eb5e855106375ed71326287d8fadf756425d0` | V |  | X |  |
| crates/aspis-r1-cost-probe/src/semantic.rs | `75d83ce86b203023c3a9a9d35420853b6a5a9196b634a971859f6f4b98b0d0c5` | V |  | X |  |
| crates/aspis-r1-cost-probe/src/semantic_wire.rs | `58c671cee016246aa464a35ba443009813581e4a53bce37dd528d048009f2db7` | V |  | X |  |
| crates/aspis-r1-cost-probe/src/trace.rs | `8315e3caed12ed8f0b3cfe097746339eec735f08c75095d1c036ac37469cf7cd` | V |  | X |  |
| crates/aspis-r1-cost-probe/src/transcript.rs | `927150f49e13feecd85ae83a46cca3f3ffdfb670346ff1846df928a6b6102889` | V |  | X |  |
| crates/aspis-r1-cost-probe/src/transport.rs | `34af7f077fdae8147ebd79a44e7acb38395ec440115109c8fbfc654cb2c1e8c7` | V |  | X | yes |
| crates/aspis-r1-cost-probe/src/verifier.rs | `8c872d42bdaa245cc540be6b26d17108a5cb40754b8befb79e147f5843b1f756` | V |  | X | yes |
| crates/aspis-r1-cost-probe/src/weights.rs | `ab55509e54218a2bfe7dd2d5e1b14216e3303961c16c181ce2e03d40f6b7678b` | V |  | X | yes |
| crates/aspis-statement/src/atomic_state_only_registry.rs | `d54ce5d801c974faeda0c0604f3ea987dd714c94ca524b8dbe00d10965edb8f1` |  |  | X |  |
| crates/aspis-statement/src/atomic_state_only_terminal.rs | `33d518ddc432866ae822917fb18a4ad5463d3fb6994fa448d097e303d937d7a9` | V | P | X |  |
| crates/aspis-statement/src/atomic_state_only_terminal_constants.rs | `f3f8d36fa293d0883fc2a6e8b26e90e679cce2af208a3c713a1599a0ed27054f` | V | P | X |  |
| crates/aspis-statement/src/atomic_state_only_terminal_constants_legacy_partition.rs | `b0a824632c92290ad4854b20706f280f34537470b86b0b30f5975c26d7db1214` | V | P | X |  |
| crates/aspis-statement/src/atomic_state_only_trace.rs | `bae98cf528cfb60af75303ed61237193d8faad508e099f22b89ed7c76bde90d0` |  |  | X |  |
| crates/aspis-statement/src/atomic_statement.rs | `c73fc9a55dd3493ae264231eaaf495c886c42cf0e58412bdb11053a191eb860a` | V | P | X |  |
| crates/aspis-statement/src/constraints_v4.rs | `264921454f5ddd97184944b149b7f41ed791230413ba80fe09eb9be7059d1ba5` | V | P | X |  |
| crates/aspis-statement/src/direct_range_hiding_v4.rs | `9d7942805b60905d7e8bf08616e34737957be4d1b9f102ef06cff68dbadee258` | V | P | X |  |
| crates/aspis-statement/src/hiding_v4.rs | `bebc2d716cb6828c38d909243b8d8cec9b56460ae38955f0f140ed71e6f19924` | V | P | X |  |
| crates/aspis-statement/src/lib.rs | `4026f1172b275a891851784b7de46268460d24a156f540328a63d88ea8078442` | V | P | X |  |
| crates/aspis-statement/src/logup.rs | `c6e84617e6473f014fc53c704dd26b04667046211985ea6ddca8f66f496bea65` | V | P | X |  |
| crates/aspis-statement/src/pool_v1/authorization_receipt.rs | `3bc828edc06170d76a67df1d97cb6ed3075897737a077dd7017c3b3cb8b13e9c` | V | P | X |  |
| crates/aspis-statement/src/pool_v1/authorization_receipt_account.rs | `132b264453c4d3c286b4d39f92b132c8e662495f809ff2ad57559d37098245cf` | V | P | X |  |
| crates/aspis-statement/src/pool_v1/deposit.rs | `86a7c004dc79805063f1813637c0712779bcd7dfb0292d137daf017a3ab9be74` | V | P | X |  |
| crates/aspis-statement/src/pool_v1/format.rs | `209bf45ab1fbf03fa6a5b524e6b2079068537368b02837e320d708ca5128f88d` | V | P | X |  |
| crates/aspis-statement/src/pool_v1/historical_anchor.rs | `2a17bc3d55209daca56af72bfa8084f240bdc6c16890ec670400c02512cb8935` | V | P | X |  |
| crates/aspis-statement/src/pool_v1/incremental_merkle.rs | `1b32061871f52a74ddbc2a9cdaa6a884ec6dd04b41fec55926631496506faa81` | V | P | X |  |
| crates/aspis-statement/src/pool_v1/mod.rs | `9fca69f290b90e77f9ccb6920acb927520099629566f3f78b474824c412ffd7e` | V | P | X |  |
| crates/aspis-statement/src/pool_v1/nullifier_marker.rs | `61baff8c01f8ac3eb2781378ca87f01e6e132c4a8722acd6bc18619449dcd4b2` | V | P | X |  |
| crates/aspis-statement/src/pool_v1/pair_constraint_residuals.rs | `c59a9033e814781b90f67c2dd6d91ddc3b7d4a0ea4a5af9a11f8be70db990e95` |  |  | X |  |
| crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs | `1992026c00dbced3a0c475b6e2be0a72fae1a7e859dd041e741707384e727ba3` | V | P | X |  |
| crates/aspis-statement/src/pool_v1/pair_forest_constraint_residuals.rs | `7bafd96ef01b1013fe587777860d4be3b48acd3043c87ce618a28c2cc02638f8` |  |  | X |  |
| crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs | `e1315ebd09abcb752e592081fbc6b4d5cf68404662a92173bc1139a5a34d88c0` |  |  | X |  |
| crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs | `f38ca2bd28554e8f67b75b7b035f02648ea0b5d82f78d2457e10188e6402a3f0` | V | P | X | yes |
| crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal_constants.rs | `cfce7ec499d3cfd54cf91eb88675e45d89ada5ce073fe00c78be5211204fbc50` | V | P | X |  |
| crates/aspis-statement/src/pool_v1/pair_forest_hiding.rs | `61bcd59a22c9c02fe3f9ba69cda43bfa8fe02ea14f15da9b761e976fe48798bf` |  |  | X |  |
| crates/aspis-statement/src/pool_v1/pair_forest_semantic_oracle.rs | `930c9f2211f1bc672195802d6e5de05588a37b48f770d805a5b2d240c8bbf344` |  |  | X |  |
| crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs | `4e209947ac75532af1c7d79f339050aab6b57379fc3962e1df9ff5602087787e` | V | P | X | yes |
| crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal_constants.rs | `68004ad1e56fba9947b8aa6f52b7eec6f3b8e9c1cfea671338945f7aa1f28111` | V | P | X |  |
| crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs | `060eaa71de4d736fad4019a0445d75345709d3fdd695ff0c0320508a3444e8e8` | V | P | X |  |
| crates/aspis-statement/src/pool_v1/pair_forest_trace.rs | `c8fb171a18b3cfb276fac6b428bc9ab8e411b464bf7d8bf00c71e84178ba8723` |  |  | X |  |
| crates/aspis-statement/src/pool_v1/pair_terminal.rs | `03fc14126dab7d78688d6fab1d954cc116357f349652a37dee5b044d45e0bbea` | V | P | X |  |
| crates/aspis-statement/src/pool_v1/pair_trace.rs | `bbb7028f4da6c420452af1bda893ec6bc490ee4e9a6a7cf561694ff73767c184` |  |  | X |  |
| crates/aspis-statement/src/pool_v1/pair_tree_hiding.rs | `3dfe485fc2e9a643a15e0bc7ef0d9fed20b1fa43984bb1d0997d38a380a90ab6` |  |  | X |  |
| crates/aspis-statement/src/pool_v1/pair_tree_profile.rs | `660f00d91fb08e809b8f00a7e3917d546cf2097e6ea4b59b951e0dc8cc03e7af` | V | P | X |  |
| crates/aspis-statement/src/pool_v1/payment_constraint_residuals.rs | `442a8702cf5eb9235ec7651d267b4761444102cafa7400d6c7c095f41eeaf860` |  |  | X |  |
| crates/aspis-statement/src/pool_v1/payment_hiding.rs | `d0b272c3e278c3428b668a3e95e762831a8981e2c20ec449fa69ef155abc5f70` |  |  | X |  |
| crates/aspis-statement/src/pool_v1/payment_relation.rs | `5651470e36353697bd5b5cdb8f6963b4cc3c4cba53bc082824fd7dcd5960b49d` | V | P | X |  |
| crates/aspis-statement/src/pool_v1/payment_semantic_oracle.rs | `2f203c385bbbf4aea00f580c29aa2d3d1db2b1dcb02b58b566ff09c6a76a2a32` |  |  | X |  |
| crates/aspis-statement/src/pool_v1/payment_semantic_registry.rs | `b3f8ad0ace248c6d4c53715116f552d884cbd08a7bc17342081d19c4d20698b1` |  |  | X |  |
| crates/aspis-statement/src/pool_v1/payment_semantic_terminal.rs | `291fd012c16a0a6eae64252707c065ee6fb7ef32ad2ab5405f092be930f09511` | V | P | X |  |
| crates/aspis-statement/src/pool_v1/payment_semantic_terminal_constants.rs | `8e042b07ed259f8b408d097453dff1a9f946b0e21423e0f746f84806bd3898d7` | V | P | X |  |
| crates/aspis-statement/src/pool_v1/payment_trace.rs | `8dba76d6fe6f19d2b800118855612e4dde1e5ef9869d14df2fbd96861dc288d2` |  |  | X |  |
| crates/aspis-statement/src/pool_v1/root_history.rs | `096ea4ced70dee6c4638eb060b5ab299ff9742c9cd199a821c5c8521ff97711f` | V | P | X |  |
| crates/aspis-statement/src/pool_v1/tag73_native_profile.rs | `78666fb8448c0db86d21a7cac7e524248edbf650579abf996e69e3f413237328` | V | P | X |  |
| crates/aspis-statement/src/pool_v1/tag73_pair_forest_profile.rs | `1f3f06d55e891dfcdfb5777380762d7595c109559b12f164d96001c6ddb2d7c5` | V | P | X |  |
| crates/aspis-statement/src/pool_v1/verifier_dispatch.rs | `fbfa90d9d8de5a36b476786132c52f7c64ee7b75a5ec3a89ea0c18d76e77c8bb` | V | P | X |  |
| crates/aspis-statement/src/pool_v1/verifier_registry.rs | `594f8b53e6c8d7cd6265542e7730c5371f3233d778de06d220bedab7529d97d9` | V | P | X |  |
| crates/aspis-statement/src/poseidon2.rs | `4563a7192a69748ab0a56ddc023a9f13f2d96d0064cd829dd17ac358bce1a740` | V | P | X |  |
| crates/aspis-statement/src/r0.rs | `e82c82f9d553530fedf22c9e7c60ffc69015e31809bf6cb76d58abdd4ecac5d3` | V |  | X |  |
| crates/aspis-statement/src/spend.rs | `16a340ea7fd1c69d83c4720fa63c096f060c2ce58f91b8c6e793ffb7913546a4` | V | P | X | yes |
| crates/aspis-statement/src/state_only_constraints.rs | `e2be03ea1c8a3912f2e850b34a40066ce9b8aff4c51bed4f093f9717d71b74d8` |  |  | X |  |
| crates/aspis-statement/src/state_only_poseidon.rs | `4467d15c9d473cbd42caf33f21aa0192bed007b58ccaa4a61cb5691532cab7fe` | V | P | X |  |
| crates/aspis-statement/src/state_only_semantic.rs | `fdea5d4d8be1dd4a093e2b06391d3f242866648496ed791a03597b596719fdd4` |  |  | X |  |
| crates/aspis-statement/src/state_only_spend.rs | `7b7a8c6be04f16be0cb0c38e4ab6c304e1ca106771113b5aad27333b1d7ed7b5` | V | P | X |  |
| crates/aspis-statement/src/state_only_terminal.rs | `1e4ae2058a92c0c8fb6217144ac0c092e233ab4dd8f4e63a85cdab7b2ae121a5` | V | P | X |  |
| crates/aspis-statement/src/state_only_terminal_constants.rs | `fd14b8dfd2f690d588b39ecabad46d23ef8b47fc9aad047f0c645260b94c99dd` | V | P | X |  |
| crates/aspis-statement/src/state_only_trace.rs | `43eeed8cb0d07d3eba63008156fdb0ec6dcac63f735e2235e5db5bc4ccb80574` |  |  | X |  |
| crates/aspis-statement/src/state_only_verify.rs | `7474d788882e79a5ecf7d2b5adbc33f88ad88f0876c1181cf822a5953a80253f` | V | P | X |  |
| crates/aspis-statement/src/trace_v4.rs | `60e36ebb52b003de401c014eb6a139f1981b19b06f575dad5b87d8f59d0c8aa3` | V | P | X |  |
| crates/aspis-statement/src/wide_v4.rs | `9037d0176d1a77288a7429e2023ca2e474e8340a4992ffeb5f9eb27dabfacbff` | V | P | X |  |
| docs/research/v8-r0-zk-20261009/refine/blockwriters/src/lib.rs | `f5ca7ae8ba4271bd9b189b2c27d3b5ee75407598c3bde90e640f6e9b491a8782` |  |  | X |  |
| docs/research/v8-r0-zk-20261009/refine/diffharness/tests/glue_gen.rs | `1fa3ed853c7805111e192993e4f13928d0c9638385fe6bc943c6ff34208a0059` |  |  | X |  |
| docs/research/v8-r0-zk-20261009/refine/poseidon/src/lib.rs | `2591c007c8dd60d4a48e75906b429b09c22d914fc25ff15b926335162af9872c` |  |  | X |  |
| docs/research/v8-r0-zk-20261009/refine/writers/src/lib.rs | `20b9aed5bfe6e41b37bdae823c1468a7a208840f03689850cf2d478fda7a8da1` |  |  | X |  |
| programs/aspis-pool/src/deposit.rs | `e1dfc108c21b37057e2f06affd38e1c3b74b8435154a331a6428d9877315691f` |  | P |  |  |
| programs/aspis-pool/src/deposit_transport.rs | `132a5df3d8488aced2c067f38c2e3a32139a28097a3ed049c27932bd0bfa2776` |  | P |  |  |
| programs/aspis-pool/src/empty_roots.rs | `c0c7542f8102d6d7fb3fc1c8a968789749079dc2e9029fd88091129d4a469867` |  | P |  |  |
| programs/aspis-pool/src/error.rs | `7a70c51c3a2f8e9ca09370f530704089ce2c85c658c1e6d7131fd984ebd17d2e` |  | P |  |  |
| programs/aspis-pool/src/history.rs | `d44f5ac4d934a83217b325118705577304db420272b839db68da7722e8f8f647` |  | P |  | yes |
| programs/aspis-pool/src/instruction.rs | `5241bf2532adf86172001fa2d6e498c1c8e8cfef5a4e7babf23406f1c6438b1a` |  | P |  |  |
| programs/aspis-pool/src/lib.rs | `3e1abdb21c64f28f6ab3b712e0ee332c76e845046dc6be6bddb4511fa6e980d7` |  | P |  |  |
| programs/aspis-pool/src/nullifier.rs | `521ec7db1e6816fd943a10a82698db32f3ee943e09ddf95425c7e8798302b2fa` |  | P |  |  |
| programs/aspis-pool/src/pair_dispatch.rs | `3a14531a6bc46da227e4853bcfb9acc16ec736db13138cdcb976013891ddf922` |  | P |  |  |
| programs/aspis-pool/src/pair_forest.rs | `d9589cfde4f9c74c022850ba624f359b6dc35efa211ce1b117042f6984d085e4` |  | P |  | yes |
| programs/aspis-pool/src/pair_forest_dispatch.rs | `95f1d6188c6102ab5724cd9791e96d77c519cb3e88dba09a52532f7882f43ad8` |  | P |  | yes |
| programs/aspis-pool/src/pair_processor.rs | `00e4f7cbb614cd5b5f9f8ff12da80c7f1eb58896f9ce6279914f448f76926b86` |  | P |  |  |
| programs/aspis-pool/src/pair_state.rs | `7ea297133ba90fbf63a4809cbefb7868364833e1007c5f97d9283f52fc9bd97c` |  | P |  |  |
| programs/aspis-pool/src/processor.rs | `dbf45b2651fdc863c218cc0e198e026594f12d0163f6b94da92b2f7486f40e49` |  | P |  | yes |
| programs/aspis-pool/src/registry.rs | `2283b3c0275d5d8db93368b3d7a7e5d456252af1854a135dd17381701981e236` |  | P |  |  |
| programs/aspis-pool/src/state.rs | `7b5b93958819169a3f59401dcca6a1f5b2183e2787b083cca2682f0c41f03dad` |  | P |  |  |
| programs/aspis-pool/src/vault.rs | `2c7d7a6ae600c42d000f131cfb86ed2ebda54e5df33d7ec4fce9a02dae1418ec` |  | P |  | yes |
| programs/aspis-pool/src/verifier_dispatch.rs | `04f7a27f5ef542a5e27d3f83679ff70db1adf8838909fe18fcbbe693bde93b81` |  | P |  |  |
| programs/aspis-verifier/src/v7_pair_empty_roots.rs | `c3b1f0f98912005d2d00a8428eeca2b0ddcb86ac0d0009f4713a1949d4dfc8a9` | V |  | X |  |
| programs/r1-cost-probe/src/deployment_ids.rs | `4d7a90081d8c3f0f46f6e80699786a1b1410dff6fd1b46bd106b6330ed9714de` | V |  | X |  |
| programs/r1-cost-probe/src/lib.rs | `e56fd18185d72d5b925da56fdd168a05c9bfea2da1c2d17058d097f74c66d4d8` | V |  | X |  |
| programs/r1-cost-probe/src/pool_route.rs | `43cfa25ec59e5349773599924d318a4b8fda923c4958760fcf1482d8fb2db9f0` | V |  | X |  |
| programs/r1-cost-probe/src/r1_pool_adapter.rs | `09ce3b480cf772c843315b9bcdabd9bf266f4065e5a524ae2a4d5560ea4feaf3` | V |  | X | yes |
| programs/r1-cost-probe/src/r1_pool_adapter_owned.rs | `246d96b479ef552b485a51a2a3d4c4dbe1ff4ef9c0527b6f9a872f296b60576b` | V |  | X | yes |

## Shared files: verifier-cone files that contain prover-gated items

Seven files are in the verifier cone and also contain items gated on `prover`/`r1p-check`. All
seven are in crates/aspis-r1-cost-probe/src, and all are also extraction inputs. No file of
aspis-core, aspis-statement, programs/r1-cost-probe or programs/aspis-pool mentions either feature.
In the table, "V" is the predicate's value in the deployed build and "+P" is its value with prover
on.

| File (path in ELF?) | Lines | Predicate | Item | V | +P |
|---|---|---|---|---|---|
| lib.rs (no) | 11-12 | feature = "prover" | `extern crate std;` | off | on |
| | 20-21 | feature = "prover" | `mod prover` | off | on |
| | 23-25 | feature = "r1p-check" | `mod RealR1_client` | off | on |
| | 26-27 | feature = "prover" | `mod dense` | off | on |
| | 29-30 | feature = "r1p-check" | `mod sim` | off | on |
| | 32 | feature="prover" | `mod host_sumcheck` | off | on |
| | 33 | feature="prover" | `mod host_semantic` | off | on |
| | 34 | feature="prover" | `mod host_commitment` | off | on |
| | 43-44 | all(audit-eight-way, prover) | `compile_error!` guard | off | off |
| multiproof.rs (yes) | 227-230 | feature = "prover" | `struct BinaryTree` | off | on |
| | 231-254 | feature = "prover" | `impl BinaryTree` | off | on |
| | 288-356 | all(test, prover) | `mod tests` | off | off (test only) |
| r1_semantic.rs (yes) | 17-22 | feature = "prover" | struct fields `round_checks`, `terminal`, `masked_terminal` | off | on |
| | 95-111 | **not(prover)** | `fn semantic_round` (verifier variant) | **on** | off |
| | 105-108 | feature = "prover" | block inside the verifier variant (dead in V) | off | n/a |
| | 113-129 | feature = "prover" | `fn semantic_round` (prover variant) | off | on |
| | 131-179 | **not(prover)** | `fn semantic_rounds` (verifier variant) | **on** | off |
| | 136-137 | feature = "prover" | `let mut round_checks` inside verifier variant (dead in V) | off | n/a |
| | 181-229 | feature = "prover" | `fn semantic_rounds` (prover variant) | off | on |
| | 233-234 | **not(prover)** | `let (running, alpha, mut transcript)` in verify_finish | **on** | off |
| | 235-236 | feature = "prover" | `let (…, round_checks)` in verify_finish | off | on |
| | 268-287 | feature = "prover" | trace block in verify_finish | off | on |
| | 301-306 | feature = "prover" | struct-literal fields `round_checks`, `terminal`, `masked_terminal` | off | on |
| r1_wire.rs (yes) | 35 | feature = "r1p-check" | enum variant `ActivePole` | off | on |
| trace.rs (no) | 3-4 | feature="prover" | `thread_local! VALUES` | off | on |
| | 7-8 | feature="prover" | push statement in `value` | off | on |
| | 9-10 | **not(prover)** | `let _ = …` in `value` | **on** | off |
| | 12-15 | feature="prover" | `fn take` | off | on |
| verifier.rs (yes) | 23, 25, 27 | feature="prover" | `Error` variants `Rejected`, `AttemptsExhausted`, `Entropy` | off | on |
| | 260, 283 | feature="prover" | `{a.weights[j]=weights.value(j);}` blocks | off | on |
| weights.rs (yes) | 319-323 | feature="prover" | trace loop | off | on |

Consequences for a prover-only refactor:

* The prover code in these seven files is interleaved with verifier code at item, field, variant
  and statement level. It cannot be moved out without editing the files, so a refactor that
  touches them fails "byte-identical to the pin". The proposed exception, "cfg-stripped verifier
  text identical", is necessary for such an edit but not sufficient.
* Five of the seven (multiproof.rs, r1_semantic.rs, r1_wire.rs, verifier.rs, weights.rs) have
  their path compiled into the verifier ELF as panic `Location` data, which includes the line and
  column. Deleting or inserting lines above a panic site in these files changes .rodata. That
  breaks gate (1) even when the cfg-stripped text is identical. lib.rs and trace.rs carry no
  location string, but a change in module order or item layout can still move code. Gate (1),
  rebuilding the ELFs byte-for-byte, is therefore the deciding check for any edit in G. The
  practical rule is to leave these seven files untouched and keep the prover items where they are.
* The `not(prover)` items (r1_semantic.rs 95-111, 131-179, 233-234; trace.rs 9-10) are the
  deployed verifier code and must not change.
* The aspis-r1-cost-probe Cargo.toml (in G) declares the prover's optional dependencies. Adding or
  changing a prover dependency edits a gated manifest and Cargo.lock. Such an edit is admissible
  only under the shared-file rule, and additionally only if `cargo tree -e normal,build --target
  sbpf-solana-solana` for both programs is unchanged.

## Prover-only free set (prover cone N016 minus G and the manifests): 61 files

* aspis-prover, 37 files: crates/aspis-prover/src/{lib, circle_candidate, circle_candidate_openings,
  pool_v1_pair_forest_honest, pow, r0, r0_fixture, state_only_candidate, state_only_candidate_prefix,
  state_only_circle_relation, state_only_entropy, state_only_good_spend, state_only_hiding,
  state_only_hiding_rank (+ 11 files under state_only_hiding_rank/), state_only_private_openings,
  state_only_proof, state_only_spend, state_only_spend_candidate, state_only_spend_openings,
  state_only_spend_release, state_only_zerocheck, v6_onefold_prover, v7_pair_forest_fixture,
  v8_privacy_affine_gate, v8_privacy_publication, v8_six_mask_hiding_rank}.rs.
* aspis-r1-cost-probe, 7 files: src/prover.rs, src/host_semantic.rs, src/host_sumcheck.rs,
  src/host_commitment.rs (the commitment backend), src/dense.rs, src/sim.rs, src/RealR1_client.rs.
  prover.rs and host_semantic.rs contain further `r1p-check` items, but they are outside every
  gated cone.
* c3: docs/research/v8-r0-zk-20261009/c3/{build,check}/src/lib.rs (aspis-r1-cert-build and
  aspis-r1-cert-check, which aspis-prover pulls in).
* z4 (aspis-z4b-probe, r1p-check only): docs/research/v8-r0-zk-20261009/z4/{r1p_lib, probe, z5,
  z6, z7, z8, z8b, z8c, z8d, z8e, z9, z9b, z9c, z9d, z9e}.rs.

A further 890 tracked files under the exported roots are compiled in none of the recorded
configurations. Examples are the tests/ and examples/ directories, `*_tests.rs` modules,
eight_way.rs, sim_owned31/32.rs, aspis-pool-wallet-v1, the rest of programs/aspis-verifier, and
docs. They are outside gates (2) and (3), but other evidence may pin them (tests, Kani harnesses,
Stream B's prover extraction), and this packet does not assess that. The full classification is in
NPK_CONE_FILES.json `tracked_classification`. Files under tools/ (for example the devnet_spend
client) were not examined.

## Extraction inputs for gate (3)

All 241 committed `evidence/prov-p*/…_spec.json` files on research (read at 9f24c952, the branch
point) were classified by their Charon cargo command:

| Configuration (Charon cargo args after `--`) | Host cone | Spec files | Gate spec ids in PCO_extract_specs.json |
|---|---|---|---|
| crates/aspis-core, `--features r0` | NPK_N011, 66 files, all in the verifier cone | 38 | S900, S901, S001, S002, S003, S004 |
| crates/aspis-r1-cost-probe, `--features private-leaf-salts,optimized-terminal,program-build` | NPK_N012, 148 files, 22 not in the verifier cone | 61 | S005–S022 (S005–S014 are labelled aspis-statement but use this manifest) |
| crates/aspis-statement, `--features r0,pool-v1-kernel` | NPK_N013, 131 files, 22 not in the verifier cone | 22 | (later P1 specs NEW9b–NEW12c, D12–D14r, P1F_SEM_*) |
| crates/aspis-statement, `r0,pool-v1-kernel` + the 9 optimized-terminal audit features | NPK_N014, 131 files, 22 not in the verifier cone | 71 | (P1 specs NEW4–NEW13, S005a/b, S009a, S010–S014 re-runs) |
| programs/r1-cost-probe, `--features pool-adapter,private-leaf-salts` | NPK_N015, 154 files, 22 not in the verifier cone | 16 | S902 (retired), S903 |
| Non-frozen crates (uploaded or archived reference/cut copies, own hashed sources; tools/multiproof-cone at d28944b2/8c029994; the adapter-reconstruct-432 snapshot) and 3 non-cargo specs (prebuilt LLBC, the aeneas tool build) | — | 33 | C001–C017, R001–R017 routes (P4) |

The 22 non-ELF files are the same for N012 to N015: crates/aspis-statement/src/
{atomic_state_only_registry, atomic_state_only_trace, state_only_constraints, state_only_semantic,
state_only_trace}.rs, crates/aspis-statement/src/pool_v1/{pair_constraint_residuals,
pair_forest_constraint_residuals, pair_forest_copy_builder, pair_forest_hiding,
pair_forest_semantic_oracle, pair_forest_trace, pair_trace, pair_tree_hiding,
payment_constraint_residuals, payment_hiding, payment_semantic_oracle, payment_semantic_registry,
payment_trace}.rs, docs/research/v8-r0-zk-20261009/refine/{writers,blockwriters,poseidon}/src/lib.rs,
and docs/research/v8-r0-zk-20261009/refine/diffharness/tests/glue_gen.rs. None of them contains a
prover-gated item. They are outside the ELFs, so gate (2) as worded ("the verifier programs' build
cone") would miss them. They must stay identical, or every emission of the affected configurations
is regenerated and re-proved.

Every `--start-from` root of the frozen configurations resolves to a file in the verifier cone,
apart from library roots such as `core::option::_::ok_or`. There are 31 distinct files (map in
NPK_CONE_FILES.json `extraction.start_from_files`). A root names where the translation starts,
but Charon's input is the whole crate cone of the configuration, so the cone rows above are the
operative list. The non-frozen specs read only their own uploaded sources, which are hashed in the
spec, and are unaffected by repository changes. The one exception, PCWC_E002 (NJT_claims_ref), runs
on the frozen workspace and is counted in the N012 row.

Not covered: emissions credited as RECEIPTED in PCXD (256 definitions) come from pre-P0
extractions (NMH_, NIV_ and others) whose configurations were not re-derived here. Some NMH_ spec
ids reappear as P1 re-runs above (for example NMH_E003, NMH_E013), but the older receipts
themselves were not enumerated.

## Proposed gate text

> A prover-only change is admissible against the pins 4bb3b3f (verifier) and b936275 (Pool) only if
> all of the following hold on the new commit:
>
> 1. The four ELFs rebuild byte-for-byte with the NOX_B002/B003 recipe (and the NPC retarget
>    variant, and for the Pool the NKX pool1 features): verifier default f8c0ec72…43d4, devnet
>    63ad3e9c…4299, retarget 2331ad8a…96ea, Pool e0e49c34…09dc.
> 2. Allowed change set = tracked files outside the union of the verifier cone and the extraction
>    inputs. That union is the 172 files listed in NPK_CONE_FILES.json under
>    `sets.verifier_cone ∪ sets.pool_cone ∪ sets.extraction_cone`, plus the 12 build-selection
>    files (root Cargo.toml, Cargo.lock, .cargo/config.toml, and the Cargo.toml of aspis-core,
>    aspis-statement, aspis-r1-cost-probe, programs/r1-cost-probe, programs/aspis-pool and the
>    three writer copies). Any change inside a shared file must leave the cfg-stripped verifier
>    text identical, verified by rebuilding the ELFs and regenerating the emissions. In addition:
>    a. the dep-info cones of the four rebuilt ELFs and of the five extraction configurations
>       (rerun NPK_collect.py) contain exactly the same paths as listed here, so no new file
>       enters a cone, and every unchanged path keeps its sha256;
>    b. `cargo tree -e normal,build --target sbpf-solana-solana` with the deployed features is
>       unchanged for both programs;
>    c. no file of G is renamed or moved, and no crate path or version changes.
> 3. For every frozen configuration whose cone contains a changed file, the Charon LLBC of every
>    gate spec in that configuration regenerates byte-identically. Otherwise the affected emissions
>    are regenerated and re-proved before credit.
>
> Because five shared files carry panic-location records in the ELF, an edit that shifts any line
> or column in them fails item 1. The expected admissible refactor edits only the 61-file
> prover-only set and the untracked or unrecorded remainder.

## Files

* NPK_BUILD_CONE.md (this file); NPK_CONE_FILES.json (all lists, hashes, features, cfg items,
  extraction mapping); NPK_RECEIPTS.jsonl (one row per attempt).
* NPK_analyze.py, NPK_extract_inputs.py and NPK_cfgscan.py (rerun from the worktree root:
  `python3 -I evidence/build-cone-20261110/NPK_analyze.py && python3 -I evidence/build-cone-20261110/NPK_extract_inputs.py`).
* host/NPK_build.sh, host/NPK_scope.sh, host/NPK_native.sh, host/NPK_tree.sh, host/NPK_collect.py;
  host/analysis/*_cone.json (raw dep-info collections) and NPK_ELF_PATH_STRINGS.txt; host/receipts/*
  (admission, limits, time, cgroup peaks, memory events, stdout and stderr with the rustc command
  lines); host/out/*/{cmd,env_exact,lock_*,so.sha256,tool_sha256}.txt; host/out/NPK_T001 (cargo
  tree and metadata).
* The host workspace, with the kept target directories (1.6 GB) and the three source trees, stays at
  /home/dombarker/project-offloads/codex-cx-cone-20261110 for reuse by the gate rerun.

## Failed attempt (retained)

NPK_N001..N005 ran the five extraction configurations on `src-v`. N001 passed. N002 to N005
failed with exit 101 because aspis-statement on the host target `include!`s
docs/research/v8-r0-zk-20261009/refine/diffharness/tests/glue_gen.rs, which is outside the NOX SBF
input set. This is a property of the export, not a code finding. It is also how glue_gen.rs was
found to be an extraction input. N011 to N015 reran the configurations on the NHR staged
extraction tree. The receipts are kept.

Target not yet established.
