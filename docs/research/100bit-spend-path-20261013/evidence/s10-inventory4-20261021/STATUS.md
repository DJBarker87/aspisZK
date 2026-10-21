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
