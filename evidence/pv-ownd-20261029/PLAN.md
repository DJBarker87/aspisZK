# D433 V229 execution-order plan

Exact sparse worktree `/Users/dominic/ZK/.worktrees/pv-own`; branch
`codex/pv-ownd-20261029`, candidate `1e44071977`.
Only V229: 100 Lean attempts available (63200–63299, audits 63297–63299),
at most 30 capped native scopes, zero Kani. New modules PV_OWND_.

Deployed application sources below resolve to the git blobs at this candidate;
standard-library sources resolve to rust-src 1.94.1, pinned in ownb's
`deployed-collector-sources.json` and ownc's `deployed-tail-sources.json`.
Paths beginning `alloc/` or `core/` are relative to that rust-src `library/`.
The plan is coverage, not proof credit. Finish each stage before the next.

| Stage | Deployed source location | Required result |
|---|---|---|
| 1. Initial full-Link bytes and owner | `crates/aspis-statement/src/pool_v1/pair_tree_hiding.rs:86–97,105–244`; `pair_tree_profile.rs` path-base helper/constants; `alloc/src/vec/mod.rs:525,966,993–1044`; `alloc/src/raw_vec/mod.rs:417–478` | Construct the actual 127 full-Link sequence, allocation and each initialized store, kinds and padding included; prove capacity and owner instance, shape/endpoint checks and error cleanup. No assumed incoming Valid schedule. |
| 2. Vec, IntoIter, guard and complete Result/world | `pair_forest_hiding.rs:122–132`; `alloc/src/vec/mod.rs:3827–3843`; `alloc/src/vec/in_place_collect.rs:232–355,371–386`; `alloc/src/vec/into_iter.rs:214–232,498–516`; `alloc/src/vec/in_place_drop.rs:1–46`; `core/src/iter/adapters/filter.rs` | Bind source header construction, specialization, read/advance/filter/write, owner handoffs, normal/unwind/error/abort continuations into the same world. |
| 3. Complete endpoint translation loop | `pair_forest_hiding.rs:136–143`; iterator/slice mutable traversal | Bind every producer and consumer conditional store, borrow restoration and full loop invariant. |
| 4. Reserve/realloc transport and actual pushes | `pair_forest_hiding.rs:144–171,63–85,88–99`; `alloc/src/vec/mod.rs` reserve/push/push_mut; `alloc/src/raw_vec/mod.rs` reserve/grow and allocator | Transport retained bytes and owner through 127→254 capacity growth, instantiate all 72 pushes, helper Option/Result branches. |
| 5. FlatMap allocation and destruction | `pair_forest_hiding.rs:179–184`; `core/src/iter/adapters/flatten.rs`; `alloc/src/vec/spec_from_iter_nested.rs:18–58`; `alloc/src/vec/spec_extend.rs`; `alloc/src/vec/mod.rs:3924` extend_trusted; `alloc/src/vec/set_len_on_drop.rs:1–33`; `core/src/array/iter.rs:54,332` | Fresh destination instance, two endpoint stores per Link, partial-length publication, array and source destruction including failure/unwind. |
| 6. Sort and dedup moves/initialization | `pair_forest_hiding.rs:185–186`; `core/src/slice/sort/unstable/mod.rs`; reached quicksort/heapsort/shared smallsort; `alloc/src/vec/mod.rs:2527–2647,3573` | Every selected move/copy/swap and guard, preservation of initialized prefix, final length and POD suffix handling. Capture of files alone gives no credit. |
| 7. Remaining stores and Result/world cleanup | `pair_tree_hiding.rs:239–263`; `pair_forest_hiding.rs:172–177,101–118,181–187`; Vec/IntoIter/RawVec drop and failure handlers | Finish checks, returned ownership, all intermediate drop/error/abort paths and complete world binding. Earlier stages include their own local cleanup, not deferred success assumptions. |
| 8. Consumed law | `R1Z/PV_RDB2D_CollectorProgram.lean` complete; original full value law in `PV_RDB2D_OrdinaryOriginal.lean` and associated 133 cone (ownc resource-source-manifest) | Compose the actual byte/world instance into both resource-program and value law; audit complete statements/axioms and one focused final replay. |

Own-1 applies: source-to-machine-code preservation remains V370 at D381/D386.
Runtime/allocator primitive outcomes remain rdea-1; source stores and owner
transfers are proof obligations. Rust/compiler/extractor semantic agreement is
**reclassification within existing tool trust**. T remains entropy_law,
entropy_kernel, observation. No endpoint premise is removed by a conditional
carrier lemma. No changes under crates/ or programs/, observer or simulator.
A witness-dependent event finding requires a checked same-public admitted pair.
