This is a source design note at `3da1531fced390103f4b67e7bdffb7f4672454a8`, before any new proof work. There is no production declaration named `C2Word.literalMessage`. `C2Word` is a Lean function-type abbreviation. The current executable Rust supplies roots and selected openings; the literal transcript's complete C2 word is auxiliary model data. Deriving that data needs an execution/ownership witness or the existing recorded-cut construction and its source bridge. A Digest32 or sampler equality supplies neither.

The accompanying `evidence/c2-word-origin-20261016/source-inventory.json` inventories every tracked Rust file under `crates/` and `programs/` at that revision: 440 files, including examples, tests and cfg alternatives. Both raw bytes and the pinned lexical identifier scan have zero occurrences of `C2Word` and `literalMessage`. Every file has Git-blob and SHA-256 pins. This proves the stated source-inventory negative. It does not inspect macro-expanded/generated output, untracked files, dependencies or deployed binaries, and is not a compiler theorem. The retained review's expression “C2Word.literalMessage” names an open construction obligation, not an existing Rust or Lean qualified declaration.

The source inventory below records exact declaration hashes, byte spans and complete slices. Its reproducible checker invokes only Git and Python. This note adds no Lean statement, axiom or production hook and claims no new formal result.

The literal-model constructors

`LiteralTypedWords.C2Word` is `Fin 1048576 → MixedLeafEncoding.C2Slot`; a slot is `Fin 2 → QM31Exact`. It denotes two encoded lane values at each of 2²⁰ codeword positions, not the two length-1024 semantic row arrays. `LiteralTranscript.Message.c2` stores both a byte message and such a word. `LiteralTranscript.erase` deliberately discards the word.

Two current model paths attach that auxiliary value:

- `CanonicalLiteralProof.literalMessage` selects `.c2 (wire.2 i) zeroC2` at row 2. It supplies all-zero auxiliary metadata. Its erasure/legacy/sampler theorems preserve bytes; they do not identify this placeholder with the source's H1/G words.
- `CanonicalCutEnrichedTranscript.enrichMessage` replaces `.c2 bytes old` by `.c2 bytes w.c2`. `wordsFromMaps` computes `w.c2` using `TypedRecoveredWords.c2Value`: recover the packed leaf at `i / 4`, strictly decode its four two-lane slots, take slot `i % 4`, and default to zero only when recovery/decoding fails. `rawC2Map` uses the recorded first-read cut, C2 tag `0xf1`, width 128, six base-8 path levels and the selected C2 root. The salt remains part of the leaf-recovery witness even though the word projects only packed field bytes.

The second path is an explicit pure model constructor from a recorded execution. It is not an existing Rust output object, and it does not prove arbitrary pre-existing metadata equals its result. `LiteralSemanticPrefix.parseMessage` reads `.c2 bytes word` and injects `c2Pair eK word` into the semantic callback. Thus replacing metadata preserves erasure and sampling but may affect semantic reading. The exact obligation consumed by `read_of_decodeFull_atC2` is a valid 25-message sequence with the row-2 constructor carrying this same word, plus strict full25 byte decoding. Establishing only the erased bytes is insufficient.

The executable origin and ownership of C2

The candidate host sources explicitly describe themselves as an UNPROVED cost probe. The following is the actual executable host construction available at the reviewed revision; it is not a claim that all externally submitted proofs came from this host API.

1. `prover::prove_masked_attempt` receives the caller's compiled trace and attempt secrets and passes them to `prove_masked_with_attempt`. The latter reserves the attempt, derives mask material, obtains `g` and H1 padding, and invokes `host_semantic::build_with_material`. The deterministic `prove`/`prove_masked_fixture` paths are separate fixture APIs; deterministic fixture entropy is not a production custody witness.
2. `host_semantic::build_with_helper_mode` commits C1, initializes the transcript, and draws lambda and chi at rows 0 and 1. Its helper closure calls `build_pool_v1_pair_forest_copy_helper_v1` with the compiled trace, append index, lambda and chi. It applies the H1 padding mask and checks the H1 sum. It then passes the two actual borrowed arrays `[h1, g]` to `Commitments::c2` before drawing theta at row 2.
3. The concrete implementation is `prover::Backend::c2`. It copies those arrays into owned `Backend.messages[26]` and `[27]`, embedding QM31 into WideExact. It builds a C2 `Commitment` and stores it in `Backend.c2`; its returned root is the same object's tree root.
4. `Commitment::build` selects lanes `[26,27]`, checks their field representation, computes `variant.coefficients` for each semantic array, and calls `EncodingDomain::encode`. It owns the resulting two `Word::Secure(Vec<QM31>)` vectors and retains the matching semantic messages, tree, lane indices and optional private salts. The exact candidate for an honest execution is therefore

   `word(i, 0) = transportQM31(Enc(variant.coefficients(H1))[i])`

   `word(i, 1) = transportQM31(Enc(variant.coefficients(G))[i])`.

   `variant.coefficients(rows)[j] = rows[variant.row(j)]`; the row permutation must be the actual S1/S2/D variant's permutation. Directly treating the 1024 semantic rows as the 2²⁰-position C2 word would be wrong. `transportQM31` here names the required checked Rust-QM31-to-QM31Exact interpretation, not a newly proved function.
5. The commitment builds slot-major leaf bytes with four slots and two 16-byte values per slot, then hashes those exact 128 bytes with the C2 tag and, for P3, that leaf's private salt. `fill_opening` reads the retained encoded vectors and the same tree. `prove_from_semantics` calls it for each selected query and serializes C2 bytes after the 480 C1 bytes, followed by salts and paths. It emits 22 selected openings, not the complete two codeword vectors. The owned commitment remains in the moved `Backend` through serialization; borrowed `h1`/`g` need not outlive the copying call. Private salt destruction is already source behavior; this task changes no retention or wallet/account key handling.

The verifier and account boundary

`stage1` borrows readonly proof/public account buffers, checks the candidate prefix and lengths, and passes the exact proof slice to program `first`. `first` decodes public bytes and calls `verifier::tx1`; `tx1` parses the proof, runs semantic verification, prepares opening challenges, processes its query prefix and writes the checkpoint. Stage 2 authenticates the account route, borrows the current proof/checkpoint, reconstructs public bytes, and calls `tx2_authenticated`, which binds those bytes through `resume`, processes the remaining queries and checks the relation.

`View::parse` checks the canonical C2 fields in the selected openings. `query_with_geometry` hashes `q[480..608]` and its P3 salt `q[640..672]`, checks the C2 path against `p.roots[1]`, then uses those values in the opening computation. This authenticates the supplied leaf at a selected index under explicit hash/model assumptions. It does not materialize a complete word, recover it from the root, or establish that an arbitrary submitter used `host_semantic`.

Rust borrowing and the source's metadata checks identify the buffers used within an invocation. The formal SDK/account execution projection and stable cross-transaction custody still need their own relation. B's single conditional `R16ReadonlyMetadataProjection` says what the readonly guard projects; it is not proof of the provenance of a host word, a hash log or a checkpoint. The checkpoint checksum is unkeyed. The source explicitly requires an authentic tx1 checkpoint and hash-bound proof/public buffers; a checksum alone does not supply that authentication.

Proposed derivation from execution and custody

There are two useful witnesses, with different scopes. They should not be conflated.

For an execution of the known host API, retain a mathematical execution witness tying the compiled trace and reserved material to the exact H1/G copies, the encoded vectors owned by `Backend.c2`, the selected root, and all serialized opening bytes. Define the literal word by the formula above, attach `.c2 framedRow2 word` when constructing the formal transcript, and derive its field-typedness and opening projections from these owned vectors. The witness can be ghost/existential proof data; it need not serialize private vectors or expose masks/salts. Derive the same concrete QM31 field transport, variant permutation/encoder, packing, salt grammar, tree/path, and callback relations from the pinned source. This would establish the constructor for honest-host executions only. No current accepted extraction establishes this full chain.

For arbitrary accepted proofs, use the already-defined recorded-experiment compiler rather than assume host provenance. `RawCutProverCompiler.compiled` records the original prover-plus-byte-verifier experiment; `RawCutWordsFromView.buildWords` reconstructs the actual commitment frames from the finite view and calls `wordsFromRawCuts`; `enrichMessage` attaches the resulting C2 word. The witness must be the complete chronological oracle experiment (including the adversarial prover's calls), not merely a host counter or on-chain verifier digest trace. The latter can omit the earlier leaf/tree calls needed at the first C2 commitment read. Default-zero unrecovered coordinates are part of this total extracted word; equality to the honest host's entire word needs successful recovery at every coordinate and cannot be asserted from 22 openings alone.

The source bridge must derive, rather than assume as a chosen equality, these facts:

- The actual held public/proof buffers, variant, parsed row-2 root and selected query leaf/path/salt bytes correspond to one execution and the same later authenticated checkpoint. Account guards, custody, checkpoint authentication and no-collision buffer binding remain distinct premises.
- The actual Digest32 calls are represented by the recorded oracle program with exact byte concatenation, chronology, callback effects and all designated addresses. Its first C2 commitment frame is read in the complete log and its root parser returns the source root. The record has consistent answers and the required first-read budget. The existing raw-cut stability theorem additionally has the explicit shared no-bad-collision event; it is not unconditional root inversion.
- Accepted query processing supplies the successful strict C2 leaf decodes and path recovery witnesses for the same indexed packed maps. P3 uses the 128-byte value plus 32-byte salt grammar. The existing recovery/cut theorems then supply coordinate equalities under their hypotheses; hashing alone does not.
- Construct the enriched row-2 message using that word, carry it through the 33-row execution, prove the completed transcript bytes equal the full25 parsed records, and establish the actual semantic read. Only then apply the existing row-2 payload bridge to obtain the C2 callback needed by `semChalsZ_read.hread`; establish `htyped/ha` for that same context. Digest/sampler correspondence is one separate edge, never the C2 witness itself.
- Connect the actual verifier decision and its opening/semantic contexts to the byte-based decision accepted by the recorded compiler. Its existing public/acceptance/first-read preservation is a model theorem; instantiating it with the actual candidate and custody is still work. The ongoing actual verify/Prepared extraction is a different gate and cannot be cited as already completed here.

The next proof should therefore begin at a source execution/custody relation producing the exact row-2 constructor and its word witness. It should not attempt to infer the word from `p.roots[1]`, replace it with `zeroC2`, or use a sampler equality to discharge the constructor. This note deliberately leaves those proof obligations open.

Exact source declarations

The table is generated from the accompanying inventory. Hashes cover the exact slices recorded there; Rust slices use the pinned balanced-brace lexer, Lean slices use explicit top-level source boundaries. These are source hashes, not compiled theorem or #print-axioms evidence.

| Witness/declaration | Exact Git path and first line | SHA-256 |
| --- | --- | --- |
| `host-semantic-build` | `crates/aspis-r1-cost-probe/src/host_semantic.rs:45` | `729e233b404bbb523d68cdadf5261229e586046bb0f4fba49c6df1e7ff20dddd` |
| `host-semantic-material` | `crates/aspis-r1-cost-probe/src/host_semantic.rs:216` | `2ef26de4a57e297f50300932e596c091233d2d61a254d935c627b859ffa8dc29` |
| `backend-c2` | `crates/aspis-r1-cost-probe/src/prover.rs:15` | `7c32724af75a1de52ea0d4bcfb8b672913e0074f875d10c067c1c7e447893c79` |
| `backend-owned-data` | `crates/aspis-r1-cost-probe/src/prover.rs:8` | `f6d1fb0430424c23dea0f12e542f910cc26cdab99de9c689db79c8f95ad6b9aa` |
| `host-attempt-entry` | `crates/aspis-r1-cost-probe/src/prover.rs:117` | `5f24916c424c826f38881009646a53e653bdb1729e08262e16bef252db377f1e` |
| `host-attempt-material` | `crates/aspis-r1-cost-probe/src/prover.rs:131` | `a37d93849dc30b6d94fb0fdea4e634c1cd808bb7e7a7d0181f300c989efafe6c` |
| `host-proof-serialization` | `crates/aspis-r1-cost-probe/src/prover.rs:190` | `d645b25a38745165ae1d8ff6d7532bc19eca5f376c1ce1e97ae97626a724f245` |
| `commitment-build` | `crates/aspis-r1-cost-probe/src/host_commitment.rs:145` | `a795392725ad32e42458e5e109e50d88a97ee5f3579452415558e75b9f1060fb` |
| `commitment-owned-data` | `crates/aspis-r1-cost-probe/src/host_commitment.rs:99` | `4c08a37818eaa0779dcd059cea2b094054405fbb17cde83846a4c9c6bcda220c` |
| `domain-encode` | `crates/aspis-r1-cost-probe/src/host_commitment.rs:58` | `09232bca523edd77b795b7e566347474d69d6ee7019f4e1075c6b6e444815f2d` |
| `commitment-fill-opening` | `crates/aspis-r1-cost-probe/src/host_commitment.rs:231` | `bcb7700682bb3cea56c382914cee65d9213af3c5958c3df23a2b61321486d696` |
| `variant-coefficients` | `crates/aspis-r1-cost-probe/src/transport.rs:16` | `82938e83a04eff125fe57cb1762eafe375cd5a791807e60eaeda31697ad4d301` |
| `verifier-parse` | `crates/aspis-r1-cost-probe/src/verifier.rs:61` | `14d02c1405208ec96879a345f29442192a68480d1f518d6a783a9c22cd7ce9dd` |
| `verifier-query` | `crates/aspis-r1-cost-probe/src/verifier.rs:242` | `c932f58fd9f2913a3f6b619adfd191c51592b182002cf68e62d81c94d859d71e` |
| `verifier-tx1` | `crates/aspis-r1-cost-probe/src/verifier.rs:342` | `040b9e9bebc42512143c0c42cc5962593659b8c58cbd16550fd83a58b258f25f` |
| `verifier-tx2-authenticated` | `crates/aspis-r1-cost-probe/src/verifier.rs:380` | `54495074dff48e193c94fc438c87f4c59fdd366c909197c098de0310f9a869fd` |
| `prefix-parse` | `crates/aspis-r1-cost-probe/src/r1_wire.rs:292` | `96adb42a3f35dbf0c401950a85b4107bf10e91ae2579cc3222468c50f385cf2e` |
| `program-first` | `programs/r1-cost-probe/src/lib.rs:33` | `22a590467dde45b500fa56bd2d6073456221acf2c80172154a53165bac6109d3` |
| `adapter-stage1` | `programs/r1-cost-probe/src/r1_pool_adapter.rs:928` | `2d17a40061a265b9b67b4bf7d932176d3fe7a8e62e238ffe0753ecf4cc9d2e57` |
| `adapter-stage2` | `programs/r1-cost-probe/src/r1_pool_adapter.rs:974` | `4a504f1898ebbd2dbc969f08cbc89afd21e26ee432975fff573a709290181139` |
| `readonly-buffer-wrapper` | `programs/r1-cost-probe/src/r1_pool_adapter.rs:184` | `a689595c5dc95f770b6edf68d7382f399421362463dc6532718df003d79806b2` |
| `helper-h1-origin` | `crates/aspis-statement/src/pool_v1/pair_forest_semantic_oracle.rs:171` | `f0f8332e6d0a7e2dcce01f58df000786b283f7b2e0b0d920d6352ab0a493b770` |
| `helper-h1-padding` | `crates/aspis-prover/src/state_only_hiding.rs:297` | `2c4fe9b8bb44de9c398b9e344b81f482e5502fe4a78f22ca98730ed05b235ba3` |
| `private-c2-leaf-grammar` | `crates/aspis-core/src/state_only_private_merkle.rs:40` | `f19b9d271783676442d5c9ddf6f620cb6e35709060a10cbfd0e8e71e738ee7b0` |
| `model-c2-word-type` | `docs/research/100bit-spend-path-20261013/lean/LiteralTypedWords.lean:17` | `517aa1b2952dfeca5572288354194f67247f63d27b886e60f1c05d32211e618a` |
| `model-c2-slot-type` | `docs/research/100bit-spend-path-20261013/lean/MixedLeafEncoding.lean:14` | `8c305f847afd6b20e8ce7ec02b9fe9edb51848bd37bd31041723686697426dd1` |
| `model-message-carrier` | `docs/research/100bit-spend-path-20261013/lean/LiteralTranscript.lean:27` | `65b3af3e4203f288a2f3fddeaeda1fd92f21e9eb4d7d690fe8fa22d1e8ed3bf2` |
| `model-erase` | `docs/research/100bit-spend-path-20261013/lean/LiteralTranscript.lean:33` | `a95eedf0cbc6cff27a97603396f076eb4ce50aa85082f49984d44a7ef13aa8c1` |
| `canonical-zero-c2` | `docs/research/100bit-spend-path-20261013/lean/CanonicalLiteralProof.lean:40` | `c66bdf71d0066b63979a770097f08201cd68572fee2113c5c86d79db6f04f8e9` |
| `canonical-literal-message` | `docs/research/100bit-spend-path-20261013/lean/CanonicalLiteralProof.lean:43` | `efb42574cd4af5cd1acaed5889016e6d5ce93536889500aa2fffead3963ec11b` |
| `cut-words-from-maps` | `docs/research/100bit-spend-path-20261013/lean/CanonicalCutEnrichedTranscript.lean:38` | `8cae31b4eb8539047ceeb037f733c1edc3bd82d72300c48b3271943411b1589c` |
| `cut-c2-packed-map` | `docs/research/100bit-spend-path-20261013/lean/CanonicalCutEnrichedTranscript.lean:56` | `cf2c4d8df2f5aa08df326aa85f478bcb51d085bf1e0c0be6da87b08e03b62b2a` |
| `cut-enrich-message` | `docs/research/100bit-spend-path-20261013/lean/CanonicalCutEnrichedTranscript.lean:150` | `f78cf3e10774c537a868db4b9c22de32ccafad1412e82274bc25de01208861ae` |
| `cut-c2-value` | `docs/research/100bit-spend-path-20261013/lean/TypedRecoveredWords.lean:42` | `0e156550c693f3066d3c2c514fbf8c87f71dfe27145bf090f97bbd485a4cbc22` |
| `model-semantic-c2-pair` | `docs/research/100bit-spend-path-20261013/lean/LiteralSemanticPrefix.lean:27` | `28b987c5af2cbc802372da0a28eebeb3d652a41323cb244bbcb917dd677c268c` |
| `model-semantic-parser` | `docs/research/100bit-spend-path-20261013/lean/LiteralSemanticPrefix.lean:32` | `4c51124d566a81e9f6774ab96bdeb480ad5fd83027c2983ff0c0054bd384ff26` |
| `model-c2-read-obligation` | `docs/research/100bit-spend-path-20261013/lean/LiteralSemanticPayloadBridge.lean:215` | `2da8d5ad0363c6dc6cae1b395c2171df84df95283c5e718428394b4d5d3fa4c9` |
| `recorded-experiment-compiler` | `docs/research/100bit-spend-path-20261013/lean/RawCutProverCompiler.lean:41` | `7e286d0b89b3b63e6ad685ef2187f757120bdbb64aed2b2a69e213e584400bb8` |
| `recorded-view-words` | `docs/research/100bit-spend-path-20261013/lean/RawCutWordsFromView.lean:32` | `5aa3c68fcea65eb1eca6c4737caf6e4bb31bd6897f6d20e039e87f620df15282` |
| `recorded-view-parser-premises` | `docs/research/100bit-spend-path-20261013/lean/RawCutConstructedWords.lean:66` | `615d4dc839d6656123b74ef65d1d131532c46ece0f49f61c5ea95f04a5e20dd7` |
| `recorded-cut-recovery` | `docs/research/100bit-spend-path-20261013/lean/RawByteCutStability.lean:21` | `c6906a57da5cb54927b14882d54dc8983023eea401f1aeb839a1816e7473eff6` |
| `recorded-cut-stability-premises` | `docs/research/100bit-spend-path-20261013/lean/RawByteCutStability.lean:97` | `a3f54f63654a6ef249d57dc6101f5976170d90a752485935ca87f618dabcd3fb` |
