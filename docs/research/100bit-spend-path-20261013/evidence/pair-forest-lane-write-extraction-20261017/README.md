# Pair-forest terminal lane-write extraction

This packet extracts the production Pool helper `next_pair_forest_lane_v1`
and its small record dependency cone into Aeneas Lean. It contains no
`AccountInfo`, PDA derivation, SDK calls, instruction dispatch, or account
serialization. The next proof target is the exact successful return fields of
this helper; connecting those fields to the next invocation's decoded public
snapshot still requires the separately identified account encoder/write/read
refinement.

## Source cut and adaptations

`input/source-manifest.json` pins all copied declarations and their source
file hashes and line spans. The Pool function is from
`programs/aspis-pool/src/pair_forest.rs`, whose SHA-256 is
`2e0852f4c5dc7ba0b25ac1567b8c3e7c3a52c8038685dad34ec2f29e05eec957`, the
selected feature-source pin. Its control flow and output struct literal are
copied from lines 1164–1190. The exact statements checked are: checked old
index plus one against `verified_afterstate.next_pair_index`; inactive
frontier slots against the Pool empty-root table; then the output constructor
copies `lane.master`, `lane.bump`, `lane.lane_id`, and the afterstate index,
root, and frontier.

The isolated cut changes only the surrounding names/dependency boundary:

- the fixed `POOL_V1_PAIR_EMPTY_ROOTS` constant is an explicit `pair_empty_roots`
  argument, supplied by the source caller from that exact constant;
- the Solana `ProgramError` conversion uses a one-variant local error carrier
  for `StateHistoryMismatch`, retaining the same success/error branches;
- the production fully qualified terminal result type is the copied local
  record declaration; its fields are copied from the exact source declaration.
- the tree depth is the source constant value 20. Aeneas maps M31's tuple
  newtype to `Std.U32`; its derived equality is the exact tuple-value equality
  used in the copied frontier comparison.

The cut is therefore suitable for proving the helper's result projections.
It does not claim the error-carrier conversion, fixed-table binding, or the
account serialization/readback relationship as already proved. Aeneas initially
lists Rust core `Option<T>::PartialEq::eq` as an opaque external used by the
`checked_add` comparison. A transparent Lean model of the exact pinned Rust
implementation is staged at `source-models/LaneWriteFunsExternal.lean` (SHA-256
`5850b76a278b1953863635c9606a276e560bc7b78e5d8af301b91b4f4cefcf4d`); it
models the four `Some`/`None` cases from rustc `1.98.0-nightly
(14210df0e27ccd7d9e6a05b8085cbd438e4bbc65)`,
`library/core/src/option.rs:2438–2452` (file SHA-256
`7cf61204b05d98a95bc2e322d5fbfc1f4f91505109971917d9a7fb47151c50e6`). A
coherent replay of the source cut, loop projection, and outer successful-call
projection against that model is green. The accepted outer theorem object has
SHA-256 `f56c74f299b57f537ddb1e15f6d771a44bcdfd4c7e5204f44afaf79ee1dc8057`
and reports only `[propext, Classical.choice, Quot.sound]`.
The additional theorem `proofs/LaneWriteCheckedAddSuccess.lean` (SHA-256
`21821998544088271e8e1ac255f0edcabf38cc84fac083f9b7094e933ed0e8f9`) proves
from the same successful source call that
`U64.checked_add lane.tree.next_leaf_index 1#u64 = some
result.verified_afterstate.next_pair_index`. It compiles with exit 0 in 1.27s,
peak RSS 2,610,184 KiB, swap 0, with axioms `[propext, Classical.choice,
Quot.sound]`; object SHA-256
`1a0a4a31c07472cea5aa60177d97675524318cab9cb8e88dee53594d3952adf2`.
`proofs/LaneWriteCheckedAddValue.lean` (SHA-256
`547268ba78930240acb2bc443716f22fa8aba55c00e4d80b5d309a00011a7bd4`)
then applies the exact Aeneas `U64.checked_add_bv_spec` to conclude
`result.verified_afterstate.next_pair_index.val =
lane.tree.next_leaf_index.val + 1`; it compiles with exit 0 in 1.16s, peak RSS
2,603,604 KiB, swap 0, axioms `[propext, Classical.choice, Quot.sound]`.
The coherent Lean object chain is recorded in
`/tmp/aspis-r1-lane-write-optioneq-20261017`: Types
`0c660cb93212d3d00b1a83a68befa627b8d8e864f265ed8c79d66115f2e0b58b`,
transparent `FunsExternal` `21d08ab49a435701b007dd3697c772d80abf9ed26c25078e7d554af0e460aeb9`,
generated Funs `d4f717f9dd88c20f470f4619df4d970eab67feb39dbc9533892fd9e0cfa2d19b`,
OutputProjection `229c5ff6c8966d0f9d699d7393463796760b9668381ec0055b721faf98082e2a`,
SourceSuccess `f56c74f299b57f537ddb1e15f6d771a44bcdfd4c7e5204f44afaf79ee1dc8057`,
and CheckedAddSuccess (above). The first three use exact sources
`Types` ebafa89e00d227062b5133725ce4494afbc8bdb722cc084ac3cb52eccdd2873e,
generated Funs 951a7dbf758bc53489a4e46d5e60dcaa4eae9048bea78110d641ab6a31a7bf88,
and `FunsExternal` 5850b76a278b1953863635c9606a276e560bc7b78e5d8af301b91b4f4cefcf4d.

## Extraction receipt

The run was performed on `dombarker@100.108.41.90` on 2026-10-17 in a distinct
systemd scope with `MemoryHigh=6G`, `MemoryMax=8G`, `MemorySwapMax=0`, and
`TasksMax=128`. The expected work was a small dependency-free optimized Rust
compile, Charon translation, and Aeneas translation; observed wall time was
under one second for all stages combined. The pinned Rust toolchain was
`nightly-2026-06-01`, rustc `1.98.0-nightly (14210df0e27ccd7d9e6a05b8085cbd438e4bbc65)`.
Charon SHA-256:
`daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8`;
Aeneas SHA-256:
`959659a6aafc6a6a975b4dc67ee9d779a269b988bd44b3b31a77cf023b1709e3`.

| Stage | Command | Exit | Wall | Peak RSS | Swap |
|---|---|---:|---:|---:|---:|
| Rust | `cargo build --manifest-path input/Cargo.toml --release --offline --lib` | 0 | 0.09s | 106,304 KiB | 0 |
| Charon | `charon cargo --preset aeneas --mir built --sysroot default --start-from crate::next_pair_forest_lane_v1 --dest-file output/lane.llbc -- --manifest-path input/Cargo.toml --release --offline --lib` | 0 | 0.18s | 168,200 KiB | 0 |
| Aeneas | `aeneas -sequential -no-progress-bar -abort-on-error -backend lean -namespace AspisR1PairForestLaneWriteSourceCut -dest output/generated -subdir AspisR1PairForestLaneWriteSourceCut -split-files -emit-json -print-unknown-externals -loops-to-rec output/lane.llbc` | 0 | 0.58s | 104,896 KiB | 0 |

The copied stage logs and Aeneas outputs are under `output/`. The generated
function is `AspisR1PairForestLaneWriteSourceCut.next_pair_forest_lane_v1`;
its loop is emitted as
`AspisR1PairForestLaneWriteSourceCut.next_pair_forest_lane_v1_loop`.

## Current proof status

The generated enumerate loop is proved by Aeneas `fixpoint_induct`: every
successful loop result preserves the old bump/master/lane ID and takes the next
index/root/frontier from the verifier afterstate. Source: `/tmp/LaneWriteOutputProjection-v5.lean`, SHA-256
`b8ca21ffb82e5293637f9badeabb78e2d0556dff266423f1562ca886978327f9`; target
`AspisR1PairForestLaneWriteSourceCut.OutputProjection.loop_success_copies_lane_and_afterstate`;
exit 0, 3.327s, peak RSS 2,623,096 KiB, swap 0, axioms
`[propext, Classical.choice, Quot.sound]`. The first outer helper projection
object, built against the opaque external, was rejected by the axiom gate and
is retained as superseded evidence. The accepted outer theorem proves that a
successful `next_pair_forest_lane_v1` output preserves old `bump`, `master`, and
`lane_id`, and copies the verifier afterstate's next index, root, and frontier.
The checked-add successor equality is established separately by the theorem
above. The account encoder/write/read path still must establish that the next parsed
public snapshot is this returned lane state before the existing
`StateLink`/`StateFacts` result can be claimed.
