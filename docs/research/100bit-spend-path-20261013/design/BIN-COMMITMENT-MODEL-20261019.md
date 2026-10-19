# Binary commitment layer, model level (2026-10-19)

Branch `codex/r1-commit-model-20261019`, base f9016d0a2. Model-level Lean
for the adopted compact binary-multiproof format
(`PREREG-PROOF-SIZE-2-20261019.md`; prototype
`crates/aspis-r1-cost-probe/src/{multiproof,compact,candidate}.rs`).
New modules only, all prefixed `Bin`; no eight-way module is edited.
Receipts: `evidence/bin-commitment-model-20261019/`.

Nothing here is a source refinement. The Rust functions are mirrored by
hand; the extraction and refinement of the candidate cone is the separate
source-side job (section 6).

## Verification status

**INCOMPLETE: unverified drafts.** The first focused local compile never
started: the binding `local-lean.txt` memory precheck requires at least
10 GiB free+inactive, and every observed check remained below that threshold.
No Lean theorem or axiom result in this packet is certified. The evidence
manifest lists the proposed compile order and source hashes with null
receipt fields. The own waiting shell was stopped; no build is running.
No memory override was assumed. Source/receipt tool syntax and provenance
coverage were checked independently.

## 1. Grammar and domain separation

The broad requested assertion “tag disjointness from every other hashed record”
is false as written. `RawTranscriptFrameBytes.lean:33` (`absorb`) begins
with arbitrary state bytes, not a domain tag; `advance` at line 39 does too.
`crates/aspis-r1-cost-probe/src/verifier.rs:382` hashes arbitrary public bytes
verbatim. Taking those public bytes equal to a binary node preimage makes
the hashed inputs identical. No collision is involved. This item stops at
that obstruction; no universal separation assumption is silently added.
Binary nodes are separated from leaves and eight-way nodes by their first
byte. Particular transcript classes can instead be separated by their
length/embedded framing, where justified.

## 2. Multiproof acceptance

Draft modules `BinMerkleProgram`, `BinMultiproof`, `BinBatchDedup`.
`Accept` is a small-step relational specification of the level-at-a-time
verifier, not an extracted implementation of the mutable Rust arrays.
`missing` sorts distinct parents, visits left then right, and supplies only
absent children. A `Level` checks every occupied child against its current
value and requires the exact supplied sequence. `Accept.done` requires one
top at index zero and no leftover supplied nodes. `exact_consumption`
relates consumed length to index-only `nodeCount`.

`accepted_path` constructs a path for every active index and shows all path
node reads are in the verifier trace. `run_preserves`/`dedup_sound` establish
the preservation condition for the pure insertion-sort/dedup model;
`accepted_original_queries` transfers the path result to every original
batch entry. `PaddedAccept` checks capacity and zero remainder and passes
only `stored.take count` into acceptance; `padded_exact_count` rules out
using extra supplied nodes. Depth is symbolic; `slots_length` applies at 18
without constructing a tree or enumerating leaves.

These are draft proof bodies pending local compilation.

## 3. Binding and collision targets

Draft binary leaf/path binding retains the exact same-index slot list.
`BinOpeningBinding.openings_agree` combines its collision alternative with
the single raw-byte collision exclusion and explicit read containment.
`BinRawByteCollisionTargets.pred : Fin 5 → Bytes → Option State` has strict
left/right node readers, trailing root, root at offset 38, and state at
offset zero, in that order. It instantiates the arity-generic
`AllAddressCollision.mass`, with no input-length bound. The new accounting
is `BinCombinedMerkleCollision.kappa Q = 6 * Q^2 / 256^32`: five readers plus
one previous-output/IV component. This is an event-mass bound with an
explicit uniform first-read budget, not a measured runtime read count.
Downstream soundness callers must instantiate this event and budget; their
existing eight-way kappa definitions are untouched.

These are draft proof bodies pending local compilation.

## 4. Recovery and compiled-run word stability

The finite-table walk, log parser, recovery witness, and append stability
are ported to two children in new `Bin*` modules. `BinRawByteCutRecovery`
uses the generic output-injectivity/parsed-target chronology theorems to
recover an accepted, logged opening from the log strictly before its first
commitment read. `BinRawByteCutStability.all_paths_stable` protects all paths
at once, including `none` results, without a coordinate union.

`BinCanonicalCutWords` uses 18 binary levels for all three padded trees.
It reuses `CanonicalCutEnrichedTranscript.wordsFromMaps`, so the strict
C1/C2/folded decoders and lane projections are unchanged. C1 has 480 packed
bytes; C2 and folded have 128; all salts have 32. Folded openings occupy the
first 2^16 leaves of the padded 2^18 domain.
`BinThreeCommitmentTypedOpening.typed_opening_at_cut` and
`typed_word_stable` are decoder-parametric; the former requires an actual
successful decode, the latter preserves failure as well as success.
`BinCanonicalCutWords.wordsFromRawCuts_eq_full` specializes to the concrete
three typed words.

`BinCompiledRunWordStability` instantiates the existing recording compiler
with a binary word builder. Its cut-equality theorem is arity-independent;
only the recovery map is changed. It compares binary words recovered from
the recorded view before and after replay, without assuming metadata equals
a recovered word. The theorem concerns the existing literal protocol model,
not the newly adopted Rust verifier.

These are draft proof bodies pending local compilation.

## 5. Theorem map against the eight-way model

All paths below are relative to `lean/`. Line pins are at the branch base.
Each same-named theorem is ported to binary children; none replaces or edits
the old declaration in place. This table describes intended statements;
compile status is exclusively the evidence manifest.

| Binary theorem | Eight-way predecessor |
|---|---|
| `BinMerkle32Path.nodeInput_length` | `Merkle32Path.lean:21` `nodeInput_length` |
| `BinMerkle32Path.nodeBytes_injective` | `Merkle32Path.lean:25` `nodeBytes_injective` |
| `BinMerkle32Path.nodeInput_injective` | `Merkle32Path.lean:37` `nodeInput_injective` |
| `BinMerkle32Path.fillChild_ne` | `Merkle32Path.lean:47` `fillChild_ne` |
| `BinMerkle32Path.nodeInput_ne_of_current_ne` | `Merkle32Path.lean:54` `nodeInput_ne_of_current_ne` |
| `BinMerkle32Path.foldPath_cross_trace_collision` | `Merkle32Path.lean:89` `foldPath_cross_trace_collision` |
| `BinMerkle32Path.foldPath_injective_of_collisionFreeOn` | `Merkle32Path.lean:133` `foldPath_injective_of_collisionFreeOn` |
| `BinMerkle32Path.depth18_cross_trace_collision` | `Merkle32Path.lean:147` `depth6_cross_trace_collision` |
| `BinMerkleNodeCodec.readChildren_nodeInput` | `MerkleNodeCodec.lean:19` `readChildren_nodeInput` |
| `BinMerkleNodeCodec.parse_nodeInput` | `MerkleNodeCodec.lean:38` `parse_nodeInput` |
| `BinMerkleNodeCodec.parse_sound` | `MerkleNodeCodec.lean:41` `parse_sound` |
| `BinMerkle32Leaf.leaf_input_length` | `Merkle32Leaf.lean:17` `leaf_input_length` |
| `BinMerkle32Leaf.leafInput_fixedWidth_injective` | `Merkle32Leaf.lean:22` `leafInput_fixedWidth_injective` |
| `BinMerkle32Leaf.leaf_path_binding` | `Merkle32Leaf.lean:40` `leaf_path_binding` |
| `BinMerkle32Leaf.c1_leafInput_length` | `Merkle32Leaf.lean:74` `c1_leafInput_length` |
| `BinMerkle32Leaf.c2_leafInput_length` | `Merkle32Leaf.lean:79` `c2_leafInput_length` |
| `BinMerkle32Leaf.folded_leafInput_length` | `Merkle32Leaf.lean:84` `folded_leafInput_length` |
| `BinMerkle32Leaf.c1_leaf_path_binding` | `Merkle32Leaf.lean:89` `c1_leaf_path_binding` |
| `BinMerkle32Leaf.c2_leaf_path_binding` | `Merkle32Leaf.lean:104` `c2_leaf_path_binding` |
| `BinMerkle32Leaf.folded_leaf_path_binding` | `Merkle32Leaf.lean:119` `folded_leaf_path_binding` |
| `BinMerkleProgram.eval_pathProgram` | `MerkleProgram.lean:23` `eval_pathProgram` |
| `BinMerkleProgram.eval_leafProgram` | `MerkleProgram.lean:37` `eval_leafProgram` |
| `BinMerkleProgram.pathProgram_accepts_iff` | `MerkleProgram.lean:47` `pathProgram_accepts_iff` |
| `BinMerkleProgram.leafProgram_accepts_iff` | `MerkleProgram.lean:54` `leafProgram_accepts_iff` |
| `BinMerkleTable.lookup_mem` | `MerkleTable.lean:28` `lookup_mem` |
| `BinMerkleTable.lookup_exists` | `MerkleTable.lean:41` `lookup_exists` |
| `BinMerkleTable.targets_length` | `MerkleTable.lean:58` `targets_length` |
| `BinMerkleTable.root_mem_targets` | `MerkleTable.lean:63` `root_mem_targets` |
| `BinMerkleTable.child_mem_targets` | `MerkleTable.lean:67` `child_mem_targets` |
| `BinMerkleTable.walk_mem_targets` | `MerkleTable.lean:81` `walk_mem_targets` |
| `BinMerkleRecovery.walk_reconstruct` | `MerkleRecovery.lean:23` `walk_reconstruct` |
| `BinMerkleRecovery.recover_or_bad` | `MerkleRecovery.lean:72` `recover_or_bad` |
| `BinMerkleLeafRecovery.lookupLeaf_mem` | `MerkleLeafRecovery.lean:22` `lookupLeaf_mem` |
| `BinMerkleLeafRecovery.recover_or_bad` | `MerkleLeafRecovery.lean:49` `recover_or_bad` |
| `BinMerkleLeafCodec.parse_leafInput` | `MerkleLeafCodec.lean:18` `parse_leafInput` |
| `BinMerkleLeafCodec.parse_sound` | `MerkleLeafCodec.lean:35` `parse_sound` |
| `BinMerkleRecordedLog.mem_nodes` | `MerkleRecordedLog.lean:27` `mem_nodes` |
| `BinMerkleRecordedLog.mem_leaves` | `MerkleRecordedLog.lean:42` `mem_leaves` |
| `BinMerkleRecordedLog.nodes_consistent` | `MerkleRecordedLog.lean:58` `nodes_consistent` |
| `BinMerkleRecordedLog.leaves_consistent` | `MerkleRecordedLog.lean:65` `leaves_consistent` |
| `BinMerkleRecordedLog.leaves_width` | `MerkleRecordedLog.lean:73` `leaves_width` |
| `BinMerkleRecordedLog.node_present` | `MerkleRecordedLog.lean:79` `node_present` |
| `BinMerkleRecordedLog.lookupLeaf_exists` | `MerkleRecordedLog.lean:85` `lookupLeaf_exists` |
| `BinMerkleRecordedLog.leaf_present` | `MerkleRecordedLog.lean:100` `leaf_present` |
| `BinMerkleRecordedLog.missing_node_absent` | `MerkleRecordedLog.lean:110` `missing_node_absent` |
| `BinMerkleRecordedLog.missing_leaf_absent` | `MerkleRecordedLog.lean:123` `missing_leaf_absent` |
| `BinMerkleTraceInputs.inputTrace_node_shape` | `MerkleTraceInputs.lean:7` `inputTrace_node_shape` |
| `BinMerkleLogRecovery.nodeInputs_subset` | `MerkleLogRecovery.lean:15` `nodeInputs_subset` |
| `BinMerkleLogRecovery.leafInputs_subset` | `MerkleLogRecovery.lean:23` `leafInputs_subset` |
| `BinMerkleLogRecovery.recover_or_bad` | `MerkleLogRecovery.lean:35` `recover_or_bad` |
| `BinMerkleWalkWitness.walk_witness` | `MerkleWalkWitness.lean:11` `walk_witness` |
| `BinRecordedRecoveryWitness.recover_witness` | `RecordedRecoveryWitness.lean:13` `recover_witness` |
| `BinMerkleLogExtension.nodes_append` | `MerkleLogExtension.lean:24` `nodes_append` |
| `BinMerkleLogExtension.leaves_append` | `MerkleLogExtension.lean:29` `leaves_append` |
| `BinMerkleLogExtension.lookup_append` | `MerkleLogExtension.lean:36` `lookup_append` |
| `BinMerkleLogExtension.lookupLeaf_append` | `MerkleLogExtension.lean:50` `lookupLeaf_append` |
| `BinMerkleLogExtension.walk_append` | `MerkleLogExtension.lean:64` `walk_append` |
| `BinMerkleLogExtension.recover_append` | `MerkleLogExtension.lean:90` `recover_append` |
| `BinRawByteCollisionTargets.pred_child` | `RawByteCollisionTargets.lean:38` `pred_child` |
| `BinRawByteCollisionTargets.pred_tail` | `RawByteCollisionTargets.lean:42` `pred_tail` |
| `BinRawByteCollisionTargets.pred_middle` | `RawByteCollisionTargets.lean:45` `pred_middle` |
| `BinRawByteCollisionTargets.pred_prefix` | `RawByteCollisionTargets.lean:48` `pred_prefix` |
| `BinRawByteCollisionTargets.fixed_frame` | `RawByteCollisionTargets.lean:51` `fixed_frame` |
| `BinRawByteCollisionTargets.trailing_frame` | `RawByteCollisionTargets.lean:62` `trailing_frame` |
| `BinRawByteCollisionTargets.prefix_of_take` | `RawByteCollisionTargets.lean:72` `prefix_of_take` |
| `BinRawByteCollisionTargets.child_node` | `RawByteCollisionTargets.lean:80` `child_node` |
| `BinRawByteCollisionTargets.mass` | `RawByteCollisionTargets.lean:103` `mass` |
| `BinRawByteCollisionTargets.child_before_node` | `RawByteCollisionTargets.lean:115` `child_before_node` |
| `BinRawByteCollisionTargets.root_before_trailing_frame` | `RawByteCollisionTargets.lean:127` `root_before_trailing_frame` |
| `BinRawByteCollisionTargets.root_before_middle_frame` | `RawByteCollisionTargets.lean:139` `root_before_middle_frame` |
| `BinRawByteCollisionTargets.duplex_state_before_frame` | `RawByteCollisionTargets.lean:150` `duplex_state_before_frame` |
| `BinRawByteCutRecovery.read_cut_iff` | `RawByteCutRecovery.lean:25` `read_cut_iff` |
| `BinRawByteCutRecovery.cut_consistent` | `RawByteCutRecovery.lean:39` `cut_consistent` |
| `BinRawByteCutRecovery.target_cases` | `RawByteCutRecovery.lean:45` `target_cases` |
| `BinRawByteCutRecovery.opening_read_of_input` | `RawByteCutRecovery.lean:59` `opening_read_of_input` |
| `BinRawByteCutRecovery.recover_at_first_commitment` | `RawByteCutRecovery.lean:72` `recover_at_first_commitment` |
| `BinRawByteCutStability.later_of_cut` | `RawByteCutStability.lean:25` `later_of_cut` |
| `BinRawByteCutStability.cut_of_later` | `RawByteCutStability.lean:37` `cut_of_later` |
| `BinRawByteCutStability.recover_stable` | `RawByteCutStability.lean:73` `recover_stable` |
| `BinRawByteCutStability.all_paths_stable` | `RawByteCutStability.lean:97` `all_paths_stable` |
| `BinGrammar.nodeInput_slices` | New exact slice concatenation; multiproof.rs:49 |
| `BinGrammar.node_ne_leaf` | New first-byte separation |
| `BinGrammar.node_ne_eight` | New first-byte separation |
| `BinGrammar.node_ne_tagged` | New generic prefix separation |
| `BinGrammar.node_ne_length` | New generic length separation |
| `BinGrammar.unrestricted_public_overlap` | Counterexample witness; verifier.rs:382 hashes arbitrary public bytes |
| `BinMultiproof.exact_consumption` | New: multiproof.rs:83-106, 191 |
| `BinMultiproof.slots_length` | MerkleIndexGeometry.lean (binary parity geometry) |
| `BinMultiproof.member_parent` | New: multiproof.rs:152 |
| `BinMultiproof.accepted_path` | MerkleWalkWitness.lean:11 walk_witness (multiproof analogue) |
| `BinMultiproof.dedup_conflict` | New: multiproof.rs:277-279 |
| `BinMultiproof.batch_accepted_paths` | New multiproof batch corollary |
| `BinMultiproof.padding_cannot_contribute` | New: candidate.rs:136-139 |
| `BinMultiproof.padded_exact_count` | New: candidate.rs:133-139 |
| `BinBatchDedup.insert_preserves` | New pure insertion-sort model; multiproof.rs:262-270 |
| `BinBatchDedup.run_preserves` | New pure insertion-sort model; multiproof.rs:273-288 |
| `BinBatchDedup.dedup_sound` | New; candidate.rs:104-132 |
| `BinBatchDedup.accepted_original_queries` | New; accepted_path plus dedup |
| `BinCombinedMerkleCollision.target_count` | RawByteCollisionTargets.lean:32 pred (11 → 5 readers) |
| `BinCombinedMerkleCollision.mass` | CombinedMerkleCollision.lean:116 mass; raw version RawByteCollisionTargets.lean:103 mass |
| `BinOpeningBinding.openings_agree` | Merkle32Leaf.lean:48 leaf_path_binding plus raw output-injectivity |
| `BinCanonicalCutWords.wordsFromRawCuts_eq_full` | CanonicalCutEnrichedTranscript.lean:109 wordsFromRawCuts_eq_full |
| `BinThreeCommitmentTypedOpening.typed_opening_at_cut` | ThreeCommitmentRecovery.lean:18,51,84 and CanonicalTypedOpening.lean:38,74,109 (one parametric theorem) |
| `BinThreeCommitmentTypedOpening.typed_word_stable` | RawSourceC2WordBinding.lean:39 actual_c2_word_stable (model analogue for any decoder) |
| `BinCompiledRunWordStability.wordsFromRun_compiled_eq_original` | RawCompiledRunWordStabilityV8.lean:39 wordsFromRun_compiled_eq_original |
| `BinCompiledRunWordStability.wordsFromRun_compiled_eq_retainedBuildWords` | RawCompiledRunWordStabilityV8.lean:161 wordsFromRun_compiled_eq_retainedBuildWords |

### Definition provenance

Every mirrored definition/abbreviation/inductive is pinned below. New
multiproof/dedup definitions model the Rust schedule rather than copying an
eight-way Lean verifier. The tables are not extraction evidence.

| Binary module | Mirrored definitions and exact original locations |
|---|---|
| `BinMerkle32Path` | `Byte` `Merkle32Path.lean:9`; `Digest` `Merkle32Path.lean:10`; `Children` `Merkle32Path.lean:11`; `childByte` `Merkle32Path.lean:14`; `nodeBytes` `Merkle32Path.lean:17`; `nodeInput` `Merkle32Path.lean:19`; `fillChild` `Merkle32Path.lean:44`; `Path` `Merkle32Path.lean:64`; `foldPath` `Merkle32Path.lean:69`; `inputTrace` `Merkle32Path.lean:75`; `CrossTraceCollision` `Merkle32Path.lean:82`; `CollisionFreeOn` `Merkle32Path.lean:126` |
| `BinMerkleNodeCodec` | `readChildren` `MerkleNodeCodec.lean:12`; `parse` `MerkleNodeCodec.lean:15` |
| `BinMerkle32Leaf` | `Byte` `Merkle32Leaf.lean:12`; `leafInput` `Merkle32Leaf.lean:14`; `fullTrace` `Merkle32Leaf.lean:32`; `FullTraceCollision` `Merkle32Leaf.lean:36`; `c1LeafInput` `Merkle32Leaf.lean:65`; `c2LeafInput` `Merkle32Leaf.lean:68`; `foldedLeafInput` `Merkle32Leaf.lean:71` |
| `BinMerkleProgram` | `pathProgram` `MerkleProgram.lean:11`; `leafProgram` `MerkleProgram.lean:18` |
| `BinMerkleTable` | `digestDecidableEq` `MerkleTable.lean:12`; `Nodes` `MerkleTable.lean:22`; `lookup` `MerkleTable.lean:24`; `targets` `MerkleTable.lean:55`; `walk` `MerkleTable.lean:75` |
| `BinMerkleRecovery` | `nodeInputs` `MerkleRecovery.lean:13`; `Consistent` `MerkleRecovery.lean:16`; `MissingHit` `MerkleRecovery.lean:19` |
| `BinMerkleLeafRecovery` | `Byte` `MerkleLeafRecovery.lean:13`; `LeafData` `MerkleLeafRecovery.lean:14`; `Leaves` `MerkleLeafRecovery.lean:15`; `lookupLeaf` `MerkleLeafRecovery.lean:17`; `leafInputs` `MerkleLeafRecovery.lean:36`; `LeafConsistent` `MerkleLeafRecovery.lean:39`; `Width` `MerkleLeafRecovery.lean:42`; `recover` `MerkleLeafRecovery.lean:45` |
| `BinMerkleLeafCodec` | `Byte` `MerkleLeafCodec.lean:8`; `LeafData` `MerkleLeafCodec.lean:9`; `parse` `MerkleLeafCodec.lean:11` |
| `BinMerkleRecordedLog` | `Byte` `MerkleRecordedLog.lean:13`; `Log` `MerkleRecordedLog.lean:14`; `Consistent` `MerkleRecordedLog.lean:16`; `nodes` `MerkleRecordedLog.lean:19`; `leaves` `MerkleRecordedLog.lean:23` |
| `BinMerkleTraceInputs` |  |
| `BinMerkleLogRecovery` | `Byte` `MerkleLogRecovery.lean:13`; `AbsentTargetHit` `MerkleLogRecovery.lean:31` |
| `BinMerkleWalkWitness` |  |
| `BinRecordedRecoveryWitness` |  |
| `BinMerkleLogExtension` |  |
| `BinRawByteCollisionTargets` | `fixed` `RawByteCollisionTargets.lean:21`; `trailing` `RawByteCollisionTargets.lean:25`; `child` `RawByteCollisionTargets.lean:29`; `pred` `RawByteCollisionTargets.lean:32`; `event` `RawByteCollisionTargets.lean:100` |
| `BinRawByteCutRecovery` | `cut` `RawByteCutRecovery.lean:22` |
| `BinRawByteCutStability` | `recoverAt` `RawByteCutStability.lean:21` |
| `BinCanonicalCutWords` | `rawC1Map` `CanonicalCutEnrichedTranscript.lean:50`; `rawC2Map` `CanonicalCutEnrichedTranscript.lean:56`; `rawFoldedMap` `CanonicalCutEnrichedTranscript.lean:62`; `wordsFromRawCuts` `CanonicalCutEnrichedTranscript.lean:72`; `wordsFromCommitmentFrames` `CanonicalCutEnrichedTranscript.lean:80`; `fullC1Map` `CanonicalCutEnrichedTranscript.lean:90`; `fullC2Map` `CanonicalCutEnrichedTranscript.lean:95`; `fullFoldedMap` `CanonicalCutEnrichedTranscript.lean:100` |
| `BinCompiledRunWordStability.wordsFromRun` | `RawCutWordsFromView.lean:32` `buildWords`; `RawCutWordsFromRunExecutable.lean:28` `wordsFromRun` |
| `BinMultiproof` | `slot`, `slots`: binary counterpart of `MerkleIndexGeometry.lean:12` `slots`; `Active`, `Values`, `parents`, `missing`, `levelInputs`, `nextValues`, `Level`, `Accept`, `nodeCount`: new model of `multiproof.rs:83-191,195-225`; `Dedup`: postcondition of `multiproof.rs:255-288`; `PaddedAccept`: `candidate.rs:133-139`, `compact.rs:48-64` |
| `BinBatchDedup` | `Entry`, `insert`, `run`: pure model of `multiproof.rs:255-288`, `candidate.rs:104-132` |
| `BinCombinedMerkleCollision` | `Coll`: `RawByteCollisionTargets.lean:100` `event`; `kappa`, `budget`: `RawAdaptiveDecoderInjection.lean:27` `kappa`, `CombinedMerkleCollision.lean:26` `budget` (coefficient 12 → 6) |

Arity-independent theorems reused by instantiation: `AllAddressCollision.mass`
and `AllAddressCollisionTrace.outputs_injective` / `parsed_target_after`;
`RawCutProverCompiler.commitment_cut_eq` and its recording compiler;
`RawCutWordsFromView.frameFromView_eq` / `frame_read`;
`RawCutTranscriptRun.chain_eq`; the strict typed `wordsFromMaps` projections.
The existing Merkle path/table theorems have fixed `Fin 8` types, so they
cannot simply be instantiated at arity two: the new modules port their
structural proofs with `Fin 2`, literal tag 0x12, and node length 65.


## 6. What remains for the source side

After the adopted source freezes, extract/refine R12/R13/R14: binary parent
and private-leaf digest calls; strict/sorted in-range batches of at most 16;
sort/dedup preservation and rejection of conflicting duplicate hashes;
array-loop refinement to `BinMultiproof.Accept`; exact node order and
consumption; six fixed slot offsets/capacities and byte-level zero checks;
compact-to-logical reconstruction; all accepted opening reads embedded in
one consistent global byte log; C1/C2/folded frame selection and chronological
cuts from actual tx1/tx2; checkpoint provenance and stored-proof binding.

`RawSourceC2WordBinding.lean:39,70` is read as the eight-way source pattern,
not reused as a binary source theorem. No binary source extraction exists
in this packet. The unchanged typed projections and literal framing can be
reused after the new source correspondence is established. M7's binary
compiler result does not alone re-prove the M8 extractor completeness or
the M9 composed failure bound: those consumers must be instantiated with
the new maps, event, and source read budget. Privacy layout/simulator changes,
fixed-slot worst-case bounds, verifier read counts, source freeze/re-pins,
and runtime/release gates are outside this model packet.

The universal hash-input tag-disjointness assertion cannot be discharged
by extraction: it is false for unrestricted public-byte hashes. Record that
boundary in any downstream theorem rather than assuming it away.
