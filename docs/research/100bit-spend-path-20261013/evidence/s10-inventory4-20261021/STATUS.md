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

## Stage 3: constant callback operand flow

`indirect.json` retains all 152 ELF callx sites. Exact function-level raw
symbols connect 21 owned callback sites to their frozen LLVM operands and
incoming arguments; the other 131 library/vtable/formatting sites have no
emitted-source operand witness in these crate outputs. Multiple LLVM calls
are never paired to machine addresses by textual order.

`resolved.json` closes **eight compiler-level operand flows**: the three
observer sites in each verifier build have only null incoming values; Pool
sites 0x76ef8 and 0x77370 have the unique incoming function
`processor::solana_sha256` (`_ZN10aspis_pool9processor13solana_sha25617h4a996967945c4283E`).
Every forwarding function is linked, has nonempty final direct callers,
its LLVM incoming caller multiset equals the final ELF direct-caller
multiset, and its address is absent from the relocated address-taken census.
All candidate operands for each closed function agree, so no LLVM call is
assigned to an ELF callx by position. This uses the pinned compiler calling
convention/SSA boundary; it is not a Lean source refinement or an all-path
machine simulation. In particular null operand flow does not by itself prove
a source accepted-run theorem.

The remaining **144 ELF sites stay OPEN**, including context-field loads and
library formatting/vtables. The 1,602 generic/native LLBC residuals remain
separate; no generic trait is invented as a deployed call target. The
independent local replay matches every classification and 24 negative checks
reject missing incoming callers, escaping callback addresses and unknown SSA
operands. Exact resources and results are in `callback-validation.json` and
host receipts. All host scopes retain 6G/8G/0 swap/64-task limits; zero swaps.
The first extractor attempt failed on an absent raw-input `address` field;
v2 correctly decodes the address component of the pinned ELF identifier.
Both receipts and the old script are retained. `#print axioms`: N/A.

## Stage 4: kernel-checked CFG chronology

`cfg-host.py` re-extracts the complete edges behind all 140 retained block
dominance observations, checks each frozen MIR body hash, and independently
computes reachability with the preceding call block removed. `cfg.json`
retains the exact source coordinates, graphs and cut sets. Six distinct
graph/cut shapes cover both verifier builds; `dominance-map.json` maps every
one of the 140 observations to its exact Lean theorem.

`OraclePortS10CFG.dominates_of_cut` proves the generic finite-path result.
The six generated `OraclePortS10Dominance*` modules instantiate it using
explicit edge constructors and sparse Boolean marks, with one symbolic
forward-closure proof per cut. Each proof case is a direct edge/cut fact;
there is no large numeral, recurrence unfolding, `decide`, `norm_num`, or
broad simplification. The largest graph has 83 blocks. The generic theorem
compiled first, then one chunk, the remaining chunks, and the combined
`OraclePortS10StdFreeze` bridge/axioms audit. All final targets exit 0 with
standard axioms and zero swaps. The two initial generic elaboration failures
(reserved identifiers/constructor case binders) are retained, not accepted.

The largest generated chunk takes 6.777 seconds and 1,342,881,792-byte peak
RSS. The final combined audit takes 18.395 seconds and 3,492,872,192-byte peak
RSS. Exact targets, revisions, source/import hashes, exits, wall/RSS/swap and
all new theorem axiom lines are in the focused receipts and `manifest.json`.

These theorems establish chronology for paths in the exact extracted CFGs.
They do **not** construct mutable source execution or prove the `source_order`
and `model_order` fields of `OraclePortJoinSplitStdFrozen.OrderingJoin`.
In particular, source TX1/TX2 arithmetic interleaving, checkpoint/digest reads,
ordinary errors and full carriers still require a semantic caller simulation.
Coverage of the forty-label list cannot establish those identities. No final
whole-source `S10Join` or frozen `AcceptedRunJoin` instance is claimed, and no
headline premise is removed. The requested end-to-end target remains open.
