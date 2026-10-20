# Candidate 7: reuse query geometry line nodes

Candidate `2aa1b879c58a63fbc47df5a4662e808e261af41a`, exact parent `e5a93db5c9a4883245dc575eaa94742f9adeb629`.

The checked source-context equivalence preserves acceptance/error outcomes, the common query prefix and accumulation work, and ordered observer/hash work. It replaces two repeated source node steps with the cached first step and one remaining step. The cached value is proved to originate from the actual successful geometry constructor; checked indexing and range bounds are derived from the caller. No field-algebra identity is assumed.

The existing retained measurements attribute 780–791 CU to stage 1 and 947–957 CU to settlement. This proof-only work makes no production Rust or protocol change and reuses those runtime measurements. It does not establish a new machine-code or CU bound.

The source audit verifies exact parent/candidate field and domain sources; inverse-audited row fission; identical batch-inversion tail after projection to flat denominators and row count; identical accumulation tail; identical query prefix; and unchanged public query, tx1, tx2 and authenticated tx2 caller frames. The explicit source-context boundary includes the existing Rust/Charon/Aeneas/compiler/library/ownership model. These are source component and caller-context results, rather than a claim that complete transactions were newly extracted.

The original checked-index unwrap retains the inherited opaque `core.fmt.Formatter` **type**, alongside `propext`, `Classical.choice` and `Quot.sound`. There are no candidate-equivalence, cache-lineage or arithmetic-law axioms, native-decision axioms, or `sorry`. Short generated string-length proof annotations are kernel checked; enum registration and existing generic library models are transported without changing computational bodies.

## Selected focused checks

All selected targets exited zero. RSS is KiB; swaps are process swap counts. Exact commands, revisions, features, source/object/receipt hashes, direct imports and complete `#print axioms` outputs are in `GEOMETRY-CANDIDATE7-FINAL.json` and the corresponding receipts. Selected import object hashes agree.

| Module | Attempt | Wall seconds | Peak RSS KiB | Swaps |
|---|---|---:|---:|---:|
| AspisR1GeometryCandidate7.Types | geometry7-types-c | 2.005 | 2591892 | 0 |
| CuSavingsGeometryStd | geometry7-std-owned-a | 1.604 | 2574952 | 0 |
| AspisR1GeometryCandidate7.FunsExternal | geometry7-externals-e | 1.604 | 2584652 | 0 |
| AspisR1GeometryCandidate7.Funs | geometry7-funs-i | 14.832 | 3425228 | 0 |
| CuSavingsGeometryNode | geometry7-node-f | 1.604 | 2601188 | 0 |
| CuSavingsGeometryRow | geometry7-row-e | 1.804 | 2601576 | 0 |
| CuSavingsGeometryFront | geometry7-front-k | 1.804 | 2626000 | 0 |
| CuSavingsGeometryDispatch | geometry7-dispatch-c | 1.805 | 2597852 | 0 |
| CuSavingsGeometryCaller | geometry-caller-range-a | 1.604 | 2593876 | 0 |
| CuSavingsGeometryCounter | geometry-counter-a | 1.604 | 2606408 | 0 |
| CuSavingsGeometryCache | geometry-cache-j | 2.005 | 2629344 | 0 |
| CuSavingsGeometryCandidate7 | geometry7-candidate-b | 1.604 | 2614828 | 0 |
| CuSavingsGeometryStage | geometry-stage-d | 1.805 | 2638296 | 0 |
| CuSavingsGeometrySingle | geometry-single-b | 1.604 | 2586932 | 0 |

Charon and Aeneas extraction receipts are `geometry7-charon-d` and `geometry7-aeneas-d` (both exit zero, zero swaps). The archived extraction-input pins and generated Lean promotion are independently checked by `check-geometry-candidate7.py`; additional source-frame audits do not change the extracted executable inputs.

## Re-pin inventory

| Changed Rust declaration | Extracted/source-context declarations to re-pin |
|---|---|
| `QueryGeometry::for_range`, private `QueryGeometry.line_z` | `AspisR1GeometryCandidate7.{old,new}.{front,row}`, `CuSavingsGeometryFront.source_equivalence`, `CuSavingsGeometryFront.inversion_context`, `CuSavingsGeometryCache.source_success` |
| `accumulate` / new `accumulate_with_node` | `AspisR1GeometryCandidate7.{old,new}.node`, `CuSavingsGeometryNode.two_steps`, `CuSavingsGeometryRow.origin_node`; common accumulation-tail source digest and `CuSavingsGeometryCounter.accumulation_next` |
| `query_with_geometry` | `AspisR1GeometryCandidate7.new.cached_node`, `CuSavingsGeometryDispatch.selected_equivalence`, `CuSavingsGeometryCandidate7.source_query_context`, `CuSavingsGeometryCandidate7.source_caller_context`, `CuSavingsGeometryStage.source_caller_equivalence`, `CuSavingsGeometrySingle.source_public_query_context`, and exact source counter/mark order |
| Unchanged caller roots `query`, `tx1_finish`, `tx2`, `tx2_authenticated` | Exact caller source digests, literal/captured starting counter, guard and end-bound source bindings; `CuSavingsGeometryCaller`, `CuSavingsGeometryCounter.query_next` |

The cache is ephemeral; serialized checkpoint/public input/proof/transcript/challenge schedule bytes do not change. No new soundness or privacy assumption is introduced by this local source equivalence.

The final stage theorem constructs reachability internally from the literal/captured starting counter and the exact checked increment suffix. Its exported caller-loop equality exposes no cache-origin, Calls/reachability, or callback-progress premise. `CuSavingsGeometrySingle.source_public_query_context` proves the exact public single-query frame with its checked `next+1` bound derived internally; checked arithmetic failures remain observable.
