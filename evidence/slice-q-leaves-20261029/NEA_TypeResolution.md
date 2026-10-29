# Typed call-graph findings for NEB

The Q inventory is explicitly conservative. Its extension inversion/negation
alternatives must not be treated as evidence of real runtime calls.

Frozen verifier.rs:134 batch_prefix_products returns (Vec<M31>,M31); :167
product.inv() is therefore M31::inv, not CM31::inv or QM31::inv. The complete
native function's result carries the M31 type, rather than an untyped word.
The actual Port3_NativeGeometryBody.Ops.op11 signature is U32→Result U32.

Frozen field.rs:1009 self.c0.square() and self.c1.square() in QM31::try_inv
are CM31::square, a function OUTSIDE slices.Q.functions. A direct native
try_inv bridge would cross that boundary. Its norm.inv() reaches CM31::inv,
then inv_with(M31::inv), which retains rule14's function-pointer quarantine.
These are exact obstacles, never a reason to delay independent scalar geometry.

Frozen field.rs:920–921 self.c0.neg()/self.c1.neg() in QM31::neg have CM31
receivers. The self-recursive QM31::neg edge in the conservative ledger is
not a native recursion. CM31::neg at field.rs:297 calls M31::neg. Neither
receiver owner may be guessed from the outer impl owner.

This note is a source/type finding for the composition worker, not a checked
per-edge certificate and not permission to hand-edit the authoritative ledger.
No composed status is changed. NEB must instantiate the actual carrier
resolution in its composed theorem before pruning alternatives.

## Deployed accumulation correction

accumulate_batched_with_node has no Observer argument and does not call mark. Its trace::value callee uses Option-free let _=(tag,index,x) when feature prover is absent. Every deployed graph receipt confirms prover is absent from aspis-r1-cost-probe. The earlier matrix's blanket Option<fn> quarantine for this helper was incorrect; it is withdrawn. The actual blockers are BatchedWeights::push/update_residue_row and native/model basis/weight iteration and frame association. Query_values/query_loop still reach mark(obs,Phase::Query(i)) and remain quarantined; mark is exactly if let Some(f)=obs {f(p)}. No literal-None specialization is used.
