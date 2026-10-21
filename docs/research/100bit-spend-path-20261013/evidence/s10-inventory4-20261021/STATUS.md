# S10 pass 4

## Stage 1: explicit std/allocation owner

New modules only. `OraclePortJoinSplitStd.Cone` adds `trustedStd` while
retaining all thirteen old owners through `owned`. `interpret_eq` proves
ordered structural substitution with this extra cone. The separate
`OraclePortJoinSplitStdFrozen.acceptedRunJoin_of_cones` composes it into the
unchanged `OraclePortFrozenOrderJoin.AcceptedRunJoin`, including both annotated
passes. Its two caller identities remain explicit hypotheses; this is a
composition theorem, not an inhabited frozen source join.

`OraclePortStdBuilder` ports `R1Z.BuilderStdModels` with only its namespace
and introductory comment changed. It retains all nine checked array,
iterator-map and range specifications. `OraclePortStdAllocation` imports the
checkpoint Vec append/push and owned-iterator models. `filled_exact` proves
replicated bounded-Vec content on reservation success and Allocation on
reservation failure. `filled_cone_join` supplies an inhabited typed helper
model/specification cone; unknown declaration names reject. `helper_covered`
covers both reservation outcomes. This is a source-shaped library model,
not a claim that physical allocation, capacity, Drop, or the actual Rust
`try_reserve_exact`/`resize` extraction has been proved equivalent.

The generated `OraclePortS10InventoryStd` lowers every one of the forty
affected declaration labels. Only `aspis_core::r0::heap::filled` changes from
an invalid caller label to `trustedStd`; other owned labels are retained.
`heap_filled_mem` checks its membership. Six std operation families have
explicit std sites, with their builder/Vec/iterator specification references.
The owner compatibility preflight is now 40/40 and exits 0. This is not the
complete deployed inventory or the missing source Calls tree.

Focused receipts under this directory record exact commands, source/import
hashes, source revision, exit, wall, peak RSS, swap and full `#print axioms`
lines. Failed elaborations are retained; only successful final attempts are
accepted evidence. Standard axioms only in successful attempts. Shared
objects and existing Lean modules are never overwritten. No shipped Rust,
wallet keys or ELF changed; the conditional shipped-change rebuild is not
triggered. No push or merge.

## Stage 2: complete trait-alias observation scan

The new scan matches explicit `<Type as Trait>::method` compiler spellings,
including the closing `)` of an inline scope. This recovers 1,972 added
location-preserving observations: 692 in each verifier build and 588 in Pool.
Now 39/40 affected verifier declarations have explicit call/inline/mono
observations. The remaining `trace::value` body is one `return` block under
the frozen non-prover cfg; its source explicitly compiles out native tracing.
Pool has 29 observed core declarations; the eleven verifier-crate-only
labels have no Pool body and are not claimed as Pool instances.

All forty labels in all three modes remain represented in `instances.json`.
The full derived JSON is 5,643,623 bytes and stays on the host: SHA-256, size
and generator are in `instances-pin.json`. The compact committed file retains
all added observations and refers to pass-three evidence for unchanged ones.
The earlier scan and receipt are retained as a superseded matcher; v2 fixes
its missed closing-parenthesis case, rather than replaying unchanged work.

Both scoped analyses exit 0, use below 210 MiB peak RSS and zero swaps;
commands, reservations, limits and exact timing are retained. The inherited
host wrapper's `source_revision` records the frozen Rust revision; each
`*-invocation.json` separately pins the analysis script SHA and this worktree
revision. `#print axioms`: N/A, compiler evidence only.

This is improved frozen-MIR provenance, not complete final-machine inlining
or an owner source refinement. Final LLVM/ELF reachability correspondence and
source exclusion/adoption are still explicit OPEN fields. No completeness
status has been promoted by treating a compiler occurrence as a source join.
