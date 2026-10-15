# J1 NonCarryShape and Pool-program checks

Source inventory at worktree HEAD `94281d6fb07be39b7f70c0b8de115a092b86c4e2`. This locates the public transition checks and their call paths. It is a source comparison only; it does not claim a formal refinement or equivalence between the host, circuit, and Pool program.

## Host and circuit checks

The host guard is `validate_transition` in `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs:180–209`. It rejects if the source pool/deployment differ from public fields, if `source.sequence != source.next_pair_index`, if `source.next_pair_index >= POOL_V1_PAIR_CAPACITY`, or unless `source.next_pair_index.checked_add(1) == Some(after.next_pair_index)`. It sets `index = source.next_pair_index` and `carry = min(index.trailing_ones(), 20)`. For each level 0–19, it skips only `level == carry && carry < 20`; otherwise expected after-frontier is the frozen empty root if `level < carry` or the source-index bit is zero, and the old source frontier entry otherwise.

That guard is called by `composition_parts` at line 1240. Both composition and terminal evaluators route through it: `terminal_parts` calls `composition_parts` at 1302–1304, and the public `r0::Public::terminal_qm31` calls `terminal_parts` at 2044–2063. The relevant circuit/public-digest equations are also built by `public_digest_lanes` (609–694): each old source-index bit chooses an empty-root or old-frontier binding, all levels are included, and the after-root and carry-frontier node are bound separately. `semantic_packed` includes those lanes (1143–1158), and `composition_parts` evaluates `semantic_packed` (1253–1256). Thus the host precheck and the circuit constraints have related level conditions, but they are distinct code paths.

## Pool program path and exact checks

The Pool program receives the terminal request through `process_pair_forest_terminal_v1` (`programs/aspis-pool/src/pair_forest.rs:1572–1589`), which calls `process_pair_forest_terminal_with_verifier_v1`. That handler decodes/authenticates accounts and validates request/account bindings (1410–1431), invokes the verifier CPI (1485–1496), validates the authenticated result (1497–1518), then constructs the next lane image before mutating lane/page/marker state (1519 onward).

The R1 probe adapter has an analogous statement-binding path, but it is a separate executable: `reconstruct_asq8_statement` (`programs/r1-cost-probe/src/r1_pool_adapter.rs:778–805`) checks old-index plus one equals candidate index, constructs the statement from the authenticated live snapshot and candidate afterstate, and calls transfer/withdrawal statement boxing; those helpers call `validate_pool_v1_pair_forest_terminal_statement_v1` (751–775). Its ASQA scanner canonical-decodes the supplied candidate bytes (688–729); `stage1` revalidates the statement before copying the candidate into the proof account (867–897). This adapter validation binds the statement and its index, while the full transition constraints are evaluated by the selected verifier.

The program-side afterstate check is `next_pair_forest_lane_v1` (`pair_forest.rs:1154–1177`), reached through `next_lane_image_box_v1` (1357–1370) before persistence. It checks only:

- `lane.tree.next_leaf_index.checked_add(1) == Some(afterstate.next_pair_index)`;
- for each level 0–19 where the corresponding bit of **the new** `afterstate.next_pair_index` is zero, that after-frontier node equals `POOL_V1_PAIR_EMPTY_ROOTS[level]`.

It does not compare active one-bit frontier entries against the old lane frontier. Statement validation is performed by `validate_pool_v1_pair_forest_terminal_statement_v1` in `crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs:227–276`, which checks public/account bindings and delegates late-transition encoding; the late-statement encoder/decoder checks only the index increment (`pair_tree_profile.rs:529–559`, `634–638`), while afterstate transport validation checks index range and canonical digest limbs (`pair_terminal.rs:113–151`). The Pool program’s zero-bit frontier check is therefore the direct program-side shape guard visible at the persistence boundary; it should not be described as implementing every equality in host `validate_transition`.

## Reachability in the adopted R1 10/12 verifier split

The separate R1 verifier stage-one path does reach the host guard. In the R1 pool adapter, `stage1` accepts `[3,10]` or `[3,11]`, parses and validates the public statement, then calls `super::first(..., data[1] as usize)` (`programs/r1-cost-probe/src/r1_pool_adapter.rs:867–935`). `process` dispatches those instruction forms to `stage1` (`:981–993`). `first` maps the transfer/withdrawal statement to `r0::Public` and calls `verifier::tx1` (`programs/r1-cost-probe/src/lib.rs:23–28`). `tx1` performs strict proof parsing, calls `r1_semantic::verify_observed`, and only after it returns prepares the transcript and processes the first `k` queries (`crates/aspis-r1-cost-probe/src/verifier.rs:342–349`). The semantic verifier calls `public.terminal_qm31` before completing semantic verification (`crates/aspis-r1-cost-probe/src/r1_semantic.rs:111–124`); that method calls `terminal_parts` (`pair_forest_semantic_terminal.rs:2044–2063`), which calls `composition_parts` (`:1285–1309`), and `composition_parts` calls `validate_transition` at `:1240`. Therefore the current split's stage one executes the full host-side non-carry comparison before it writes the checkpoint, regardless of whether `k` is 10 or 11.

Stage two uses `verifier::tx2_authenticated` from the adapter (`r1_pool_adapter.rs:939–979`). It shape-parses the proof, resumes the checkpoint bound to the proof/public bytes, processes the remaining query range through 22, then calls `finish_relation` (`verifier.rs:368–385`). That strict R1 stage-two path does not repeat semantic parsing or `validate_transition`; the check was reached in stage one. The Pool program's statement/canonical transport checks and its narrower `next_pair_forest_lane_v1` check described above remain separate from this verifier-stage host check. This is a reachable-call inventory, not a proof that Rust refines the Lean `NonCarryShape` definition.

For a full carry, the old valid index may be `2^20 - 1`; `trailing_ones()` is 20 and the host's `carry < 20` skip is false, so all 20 levels take the `level < carry` branch and must equal empty roots. The after-index is `2^20`, whose low 20 bits are all zero, so `next_pair_forest_lane_v1` likewise checks all 20 entries against the empty-root table. The source live snapshot is still restricted below capacity, while the verified afterstate transport allows the new index through capacity.

## Source pins

| File | SHA-256 |
|---|---|
| `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs` | `2bb7db64dc53c8a268e42b0fe46da64ab1afcb03d28bbec2569b2abc30cbc074` |
| `crates/aspis-statement/src/pool_v1/pair_tree_profile.rs` | `8a7a4c7bdd3fe0ecd14d6fc920182be434ab92536924de22d269d906be3387b2` |
| `crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs` | `becc01f162f23cd9b4a7fd3780be5a441c9b7265f3078282244cc938da63a16c` |
| `programs/aspis-pool/src/pair_forest.rs` | `d96b352bae081a72d6e887759a356674598e0bf3a177c8d103885f02bc344c30` |
| `programs/r1-cost-probe/src/r1_pool_adapter.rs` | `b2adab8610189a5031fc6f28a7cdeef12c01aa292423743cb4696aa3ee1590a4` |
| `programs/r1-cost-probe/src/lib.rs` | `294546036e6cf8bb8dcc1f1f4a65c5e0887ac04593cdda801f58c75a284d582a` |
| `crates/aspis-r1-cost-probe/src/verifier.rs` | `2cab573be46ca69b5d82837e5221a9a499d3b6dc1f89b801e388b4e8b1fe01cd` |
| `crates/aspis-r1-cost-probe/src/r1_semantic.rs` | `964f008a0841246fe3638ce2e492d12d18d78302565aa57f8c7df4d079579ce3` |
| `docs/research/100bit-spend-path-20261013/lean/AppendSemantics.lean` | `b183ffbc79465d2c28b52038fa2dc1b66697583f1e57fcad0700afa28c501a39` |

`AppendSemantics.NonCarryShape` in `lean/AppendSemantics.lean:14–20` formalizes the host's non-carry frontier premise. `complete_frontier` and `afterstate_of_production` (28–80) still take that premise explicitly. These declarations are not by themselves evidence that the Pool program executes the same check.
