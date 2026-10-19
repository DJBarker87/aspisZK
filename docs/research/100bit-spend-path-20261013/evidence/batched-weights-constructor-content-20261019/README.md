# Actual BatchedWeights constructor content proof packet

This packet proves the generated `BatchedWeights.new` constructor copies every in-range source `QM31` weight into its raw row, with `terms = 0`, raw length equal to source length, and each of the four initial U64 coordinates below `2^32`. The proof derives overwrite semantics from the generated `new_loop.body` and successful `Vec.index_mut`; it does not assume reserve preserves its buffer contents.

The successful-allocation decomposition inherits the Aeneas allocator axioms `alloc.collections.TryReserveError` and `alloc.vec.Vec.try_reserve_exact`; these are explicitly present in the final `#print axioms` result. The private generated Funs owner is V7; V5 shared objects were restored and hash-verified before the V7 overlay was used. Its exact Types/Funs object bytes and owner manifest are included.

Primary theorem: `BatchedWeightsNewSuccessContentsBoundsV2.new_success_contents_bounds` (Lean module `BatchedWeightsNewSuccessContentsBoundsV3`). It includes exact actual read success at each in-range index.


## Initial global phase bound

The packet also includes `BatchedWeightsNewInitialGlobalBoundV6`: from a successful actual `BatchedWeights.new`, every raw row and every one of its four coordinates satisfies the phase-zero (`terms = 0`) `GlobalRawPhaseBound`. It uses the row contents and `< 2^32` facts above plus the pinned global-frame definition. The conclusion still inherits the explicit allocator axioms from `try_reserve_exact`. This result is not by itself the full caller query theorem; the actual `natural_range_query_global` consumer still requires source operand-canonicality and the checked counter-increment success fact.


## Query caller composition

`BatchedWeightsNewQueryCallerV8.successful_new_then_natural_query_global` composes successful actual construction with the established `natural_range_query_global` theorem. It derives the constructor's zero counter and its checked increment, and obtains exact raw length from the constructor proof. It is conditional on `n = weights.len`, `n ≤ 256`, and canonicality of each `powerAt`/`basisAt` operand. The theorem still uses the established source-shaped `rangeVisits`/`queryStep` model; correspondence from the real caller's source arrays to those operand maps remains open. Allocator axioms remain explicit.


The initial-global-bound V6 theorem now derives the phase0 cell bound for every row directly from this actual successful constructor. All21 focused compiled targets are published with exact sources, receipts, commands, source revisions, wall time, process RSS and swap. Primary outputs print their axioms; two small read helpers have no individual print and are covered transitively by those primary audits. The publication manifest expands these values from the recorded local evidence; all passed, with zero process swap. Only the final successful-allocation cone carries the two named allocator axioms, which are not presented as standard logical axioms.

The private V7 generated source and extraction kit match the previously committed bidirectional push-query packet (d189b9ac6). They do not replace the canonical V5 generated owner. Both owner/object pins and the source kit are retained so this assumption cannot be hidden by namespace lookup. Canonical copies of the proof sources are under the main research lean directory; this evidence packet retains its original frozen sources as well.

The additional V8 caller theorem derives the first checked counter increment from terms0 and supplies initialization to the proved range-query model. Its remaining premises include n<=256, source weight-length identity and canonical power/basis operands. Remaining: source operand mapping and actual source/cadence caller composition; complete verifier acceptance-to-Checks; actual universal resource/query counts; clean unified source/owner and release artifact. Constructor initialization alone does not prove those caller properties or the full100-bit claim.
