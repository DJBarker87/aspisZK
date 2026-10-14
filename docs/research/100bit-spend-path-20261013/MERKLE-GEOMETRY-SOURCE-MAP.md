# P3 semantic commitments and Merkle geometry: source map

Inspected source revision: `eac8ca7d792be9438200ec839b30102a5204881d`. This records source formulas and existing Lean statement names only. It does not assert a Rust-to-Lean correspondence.

## Domain and path indexing

- `crates/aspis-core/src/r0/mod.rs:33-34`: `WORD_LEN = 1 << 20 = 1,048,576` and `FIBRE_COUNT = 1 << 18 = 262,144 = 8^6`.
- `crates/aspis-core/src/r0/domain.rs:19-32`: `FibreIndex` is bounded by `FIBRE_COUNT`; `SlotIndex` is bounded by 4; `InitialIndex` by `WORD_LEN`. A source fibre u and slot s map to initial position `child_index(u,s)=4*u+s`; parent and slot of initial index i are `i/4` and `i%4`.
- `crates/aspis-core/src/r0/merkle.rs:15-19,31-61`: each tree has 262,144 leaves and exactly six 8-way levels. Parent input is byte `0x18` followed by eight 32-byte child digests in order (257 bytes). For leaf index i, each level's selected slot is `i % 8`, then next-level index is `i / 8`; the path includes seven other children in increasing slot order, omitting the selected slot. Six levels mean 42 sibling digests per path.
- `crates/aspis-r1-cost-probe/src/verifier.rs:120-136,252-262`: verifier uses the same bottom-up slot/index update and authenticates folded leaf at `u/4`.

## C1 and C2 leaf payloads

`crates/aspis-r1-cost-probe/src/host_commitment.rs:164-219` loops over each physical fibre `u in 0..FIBRE_COUNT`, gathers four consecutive word values `4*u+s`, and serializes slot-major then lane-major. It uses `width=4` bytes for lane indices below 26 and 16 bytes for extension lanes. The same generic builder selects the C1 or C2 lane list and tag.

- **C1:** lane list is 27 values (26 base lanes plus extension lane 28); per fibre payload is four slots × (26×4 + 1×16) = 480 bytes. Leaf tag is `merkle::C1_TAG = 0x71`; unsalted leaf input is `0x10 || 0x71 || packed480`. P3 verifier leaf payload slice is `q[..480]` (`verifier.rs:244-250`). With `private-leaf-salts`, the C1 salt is immediately after both C1 and C2 packed payloads, at query offsets 608..640 (`verifier.rs:247-250` and prover `prover.rs:245-248`).
- **C2:** two extension lanes (26 and 27), four slots × 2 ×16 = 128 bytes; tag `0xf1`; unsalted input `0x10 || 0xf1 || packed128`. Verifier payload is `q[480..608]`; when salted, its salt is at offsets 640..672.
- C1/C2 physical leaf index is the queried fibre `u`; each tree has all 262,144 physical leaves, with no padding step in these two builders (`merkle::Tree::new` requires exactly FIBRE_COUNT leaves).

## Folded commitment logical vs physical size

In `crates/aspis-r1-cost-probe/src/prover.rs:203-226`, S2 (two folds) evaluates the once-folded word, and loops over 262,144 physical leaf indices `u`. For `u < 1<<16 = 65,536`, its payload is four encoded E values `folded_word[4*u..4*u+4]`, 128 bytes. For `u >= 65,536`, payload is 128 zero bytes. Thus the constructor has 65,536 populated logical leaves followed by 196,608 zero-payload padding leaves, all hashed into the physical 262,144-leaf six-level 8-way tree. This is zero-payload padding, not a statement that the padded leaf digests are duplicated.

- Folded leaf tag is `0x72`; unsalted input is `0x10 || 0x72 || packed128` (including the all-zero packed payload for padded leaves). In P3 the 32-byte private salt is appended in the proof after each queried folded packed payload (prover `prover.rs:251-255`; verifier `verifier.rs:254-262`).
- Query `u` for the folded tree maps to logical/physical leaf `u/4` in the verifier and prover path lookup. Since `0 ≤ u < 2^18`, this accesses leaf indices 0..65,535: only the populated logical range. The folding groups four consecutive queried fibres per folded leaf.
- The post-fold coefficient/final-message transcript commitments are separate from the folded Merkle leaf geometry; prover output writes folded root and first-round coefficients at `prover.rs:224-237`.

## Existing Lean index and byte-layout statements

These are relevant existing statements; this inventory does not establish that Rust constructors refine them.

- `docs/research/100bit-spend-path-20261013/lean/Merkle32Path.lean`: `nodeInput_length`, `nodeInput_injective`, `fillChild`, `foldPath`, `inputTrace`, `foldPath_cross_trace_collision`, `foldPath_injective_of_collisionFreeOn`, `depth6_cross_trace_collision`. It models six levels and Fin 8 slots, but has no theorem connecting a Rust `FibreIndex` to the six slot digits.
- `.../lean/Merkle32Leaf.lean`: `leafInput`, `leaf_input_length`, `leafInput_fixedWidth_injective`, `c1LeafInput`, `c2LeafInput`, `foldedLeafInput`, corresponding `*_leafInput_length`, `c1_leaf_path_binding`, `c2_leaf_path_binding`, `folded_leaf_path_binding`. Fixed packed widths are 480/128/128 and salts 32 bytes.
- `.../lean/ThreeCommitmentRecovery.lean`: `c1_recover_of_no_events`, `c2_recover_of_no_events`, `folded_recover_of_no_events`, with those same tags/packed widths and salt length 32; these are table/recovery statements, not index/encoding correspondences.
- `.../lean/QueryResidualBridge.lean:21-32` uses query indices `q : Fin 22 → Fin 262144`; `.../lean/MatchingSupport.lean:45-55` defines matching sets over `Fin 262144`. These encode the query-fibre domain but not the Rust `u → u/4` path-index map.
- `.../lean/Line18Geometry.lean:27-93` and `SecondFoldRestoration.lean:358+` contain four-child (base-4) fold geometry over 65,536/262,144 indices. They concern the algebraic fold/domain map, not the eight-way Merkle sibling path.

## Source hashes

SHA-256 at inspected HEAD `eac8ca7d792be9438200ec839b30102a5204881d`:

```
709f1d0d9be9d3ee74e2b63e13065f5a91c878ba77ed2d2e97a414fbbc646aca  crates/aspis-core/src/r0/mod.rs
43bfef6f29698a4751504f9adee0e7dfdd092f6ecae6ace16f498cb2ef0fe068  crates/aspis-core/src/r0/domain.rs
6df6b25bf5b29dd2744af9db645e3c5818fa9256a454f175db4b750919ce7224  crates/aspis-core/src/r0/merkle.rs
551c4f8a0df50e0b53ab7e79d4e71b8c6afe417043c55caa1c377da3388f890c  crates/aspis-r1-cost-probe/src/host_commitment.rs
113a367ae1e01d8fbd808ce3756b87040fd31ab359d94bad50b7c55c89c284bf  crates/aspis-r1-cost-probe/src/host_semantic.rs
a7e20e5eb2fb706f2bdb51371466d4ee02c6fcabc67a427495a3b9276d9495fd  crates/aspis-r1-cost-probe/src/prover.rs
2cab573be46ca69b5d82837e5221a9a499d3b6dc1f89b801e388b4e8b1fe01cd  crates/aspis-r1-cost-probe/src/verifier.rs
34af7f077fdae8147ebd79a44e7acb38395ec440115109c8fbfc654cb2c1e8c7  crates/aspis-r1-cost-probe/src/transport.rs
93ef63727b5fc596eec0084ec737e921d54719e8a87d276cc151b3e8b2c28270  docs/research/100bit-spend-path-20261013/lean/Merkle32Path.lean
2d1f9ff2dc19bae994abbeda18ec96ae2654fecb1bc4873f2b3c4ae763f85ae8  docs/research/100bit-spend-path-20261013/lean/Merkle32Leaf.lean
e293fde75b634da5f171b982a0378fb5e3e329c84d43892381e13e4e12a15c9d  docs/research/100bit-spend-path-20261013/lean/ThreeCommitmentRecovery.lean
be0eb17ab0106a76daa08f0f313fe9f6ffddd2a6ff9960d9cf5e8e33c75a4627  docs/research/100bit-spend-path-20261013/lean/CanonicalC1Recovery.lean
```

## Supplementary native counter artifact on NUC

Existing workspace: `/home/dombarker/project-offloads/aspis-hash-input-counter-eac8ca7d`. It has no `.git` directory, so no saved Git tree object or Git status/revision is available there; the counter JSON records source revision `eac8ca7d792be9438200ec839b30102a5204881d`. The saved executable is `/home/dombarker/project-offloads/aspis-hash-input-counter-eac8ca7d/tools/r1-hash-input-counter/target/release/r1-hash-input-counter`, SHA-256 `cdb8f6f753d741fadda5c054638c59ba86f91522f70d9b0dd05de29e05093151`. Saved report `results/hash-input-counter.json` states tx1/tx2 acceptance true, checkpoint length 1768, exact full-concatenated-input `Vec<u8>` identity, 583 combined raw calls and 452 combined distinct inputs. It also identifies fixture hashes and no proof generation. Build and run logs are saved (`results/build-final.log`, `results/run-final.log`); build used `cargo build --release --offline`, run was the already-saved counter execution. No rerun performed for this inventory.

Supplemental SHA-256: `f0edc31d07d30f5b19fcaf872fba18678d13d1ba5fac1199f1f4d2be74c74f9b` for `crates/aspis-core/src/state_only_private_merkle.rs` (private leaf hash slices `[0x10, tag]`, packed value, salt32). This helper makes the salted hashed byte concatenation explicit.

NUC counter workspace supplementary pins: executable SHA-256 above. The saved `tools/r1-hash-input-counter/src/main.rs` SHA-256 is `9998ea2d172ef4fb9fd4fde721ba0ca30dc1699ca4bb9b5b765133a14151d040`; counter Cargo.toml `26cd86f1471384952ed7c0484ab9c36a81df24e03523b53a0c5c9b8480a99773`; workspace Cargo.toml `55e9bc9f106a3826e72dc782b29a013dd192a4d9b4c9c0da5f6332b095bf8fe4`; Cargo.lock `f93f8f524fdd707c7a3b7feade31d015c891264b6c8fbd8bff885249e19600ea`; saved report `5af1c64b24c64adbb8d1252cd006e1a59a4177032766e324c06e17830da3479b`. The workspace has no `.git` directory and contains no full-source-tree manifest/hash list. `results/build-final.log` records the optimized offline Cargo build and `results/run-final.log` records the already-completed execution; no measurement was rerun.

## Verification note at causal-commitment packaging

At worktree base `b0285d5afb56f158014470de4a87730547ab5738`, SHA-256 checks confirmed that each source listed above still matches its recorded historical digest from inspected revision `eac8ca7d792be9438200ec839b30102a5204881d`. This confirms byte identity for those files across the inspected revisions. It does not add a Rust-to-Lean refinement theorem: the arithmetic path geometry and byte-layout statements remain separate from source correspondence.
