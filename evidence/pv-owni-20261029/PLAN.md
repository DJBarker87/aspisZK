# D444 V239 execution plan — written before any Lean launch

Branch codex/pv-owni-20261029; base 4ae289aed7. Exact sparse worktree
/Users/dominic/ZK/.worktrees/pv-own. Recovery inspection found no owni
receipt, source, host directory or intervening commit: prior D444 attempts
0/100 Lean, 0/30 native scopes, 0 Kani. IDs 64200–64296 development,
64297–64299 audits. No other row is advanced.

## Deployed execution order

The selected op222 is aspis_statement::constraints_v4::multilinear_evaluate_qm31,
crates/aspis-statement/src/constraints_v4.rs:782–796 (not the distinct
prover-local stack-array implementation in host_multilinear.rs).

1. Read column length and compare TRACE_ROWS=1024 (:783–785). Wrong length
   returns None before allocation, field operations or cleanup.
2. sparse_eq_weights (:601–632): reverse iterate the ten public coordinates,
   literal raw equality to ZERO/ONE, count trailing Boolean coordinates
   (:602–607); subtract from ten (:608); shift/OR the Boolean suffix
   (:609–612). Control is point-dependent, never column-value-dependent.
3. Vec::with_capacity(1 << prefix_len) (:613): RawVec/allocator exact capacity,
   layout of (usize, QM31) =24 bytes/alignment8, len0 and uninitialized spare
   capacity. Null/default abort remains explicit under rdea-1. Establish
   token, generation, owner, byte extent and empty initialized prefix on the
   shared PV_OWN interface, using the deployed Rust1.94.1 Vec/RawVec bodies.
4. Prefix loop (:614–629), in increasing prefix order: row shift/OR (:615);
   ONE (:616); increasing coordinate loop (:617–626), bit extraction,
   optional ONE.sub, then weight.mul in this exact order; tuple write and
   initialized-length increment through Vec::push (:628). Prove room for
   every push and no reserve/realloc. Bind raw QM31 bodies, not canonical
   field operations substituted without transport. Then prove successful
   monadic builder has exactly 2^prefix_len entries.
5. Return weights (:631), ownership move into caller, then into_iter (:788–789).
   Vec/IntoIter constructor transfers the same allocation; each fold step
   reads and advances a POD tuple, column[row] bounds check, weight.mul(value),
   sum.add(product), in source order (:790–792). No column scan allocation.
6. IntoIter exhausted/drop: drop remaining POD elements (no destructor
   effects), then free backing store with its original capacity/layout;
   preserve panic/error/default-abort distinctions. Wrap Some (:786–795).
7. Dense-to-sparse transport: instantiate pruning/Boolean suffix and ordered
   product/fold law for arbitrary columns and raw arithmetic; do not replace
   Result failure/divergence by a success hypothesis.
8. Consuming protocol calls: state_only_candidate_prefix.rs:742–760
   point_claims passes wire::statement_points(point), all29 column slices,
   three points in order and propagates shape errors. Also :249–274
   statement_evaluations passes z, successor_point(z), xor12_point(z) and
   h1/g after base columns. Resolve the selected extracted op222 caller and
   actual transcript/public point binding before claiming whole-row credit.
   The host_semantic.rs:44 caller uses a separate stack-array backend and
   does not by itself associate the selected Vec source.

## Input-free subcalls and influence channels

The root and sparse builder have inputs: own-2''' cannot close either.
QM31::ZERO/ONE construction, element size/alignment/drop-glue selection and
TRACE_ROWS are input-free constants. Their laws can be closed symbolically;
no native singleton harness is necessary unless one is actually used.
with_capacity, push, field methods and the fold all take inputs; none is
claimed input-free. Memory primitives influence only caller-supplied memory
(V370). Allocator influence channels are success/failure, addresses and later
read state; retain rdea-1 and prove address independence, no later errno/state
read outside allocator. Source-to-machine-code remains V370/D381/D386.

## Resource and proof gates

Prove allocation request size/order as functions of public points, column
count and lengths, including early return and per-call allocation/free order.
The point itself may determine capacity; point length alone does not. Bind
point publicity at the protocol consumer rather than infer it from a name.
If same-public witnesses give different allocation/destructor occurrence,
order or size, retain a checked FINDING and stop this row.

Follow requested proof order: initialized Vec/ownership/drop first; raw
ordered methods; successful builder cardinality; dense transport; consuming
point/length. Small symbolic modules, named stage lemmas, no raised limits,
no broad concrete reduction. One admitted capped scope at a time (6G/8G,
swap0, Tasks64, Lean-M7000); verify source/object cohorts before reuse.
Compile changed generic modules first, then dependent bridge, one final
statement/axioms audit and frozen focused replay. No repeated full suite.
No shipped source, observer, simulator, dictionary, T or protected ledger edit.
