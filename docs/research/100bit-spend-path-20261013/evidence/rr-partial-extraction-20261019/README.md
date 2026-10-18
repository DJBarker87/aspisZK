# Partial RR traversal with strict abort and existing correctness contracts

The total CompPoly FieldRootContext cannot directly admit a bounded randomized root finder that can abort. Substituting an empty root list on failure would silently lose completeness. This packet provides the required partial traversal instead.

`RRPartialPrefixCollector.collectPartial` is executable, returns Option candidate lists, and propagates every reached child/root failure as failure of the whole traversal. It never interprets none as an empty complete list. Its `ready` condition asks only that the bounded tree of reached child calls succeeds; it does not require every possible state to succeed.

The successful-run refinement needs only `children? s = some cs -> cs = children s`. Under that condition, any successful partial run returns exactly the proof-only total collector output. A total completion may be used in this proof; no total field enumeration runs in the partial algorithm. Randomized child/root ordering can be incorporated into that proof-only completion for each fixed tape, rather than imposing a universal fixed ordering.

`RRPartialPrefixContracts` proves the total tree equals the existing `RRPrefixCollector.collect` and reuses its soundness and completeness theorems. Successful partial outputs inherit both under the existing exact-zero-test, local-descent and root-preservation contracts. These source-specific contracts and the root-finder/normalized-vector integration still need concrete instantiation. Probability that the traversal aborts is not proved in this packet.

Both accepted modules compiled under native pinned Lean 4.32 with exact source/object/direct-import hashes, wall time, RSS, process swap count and standard-only axiom reports in receipts. The collector definition itself has no axioms. The narrow-import accepted versions use about 0.66 GB and 1.79 GB process RSS; pre-existing host swap is recorded separately. Existing compiled caches were reused, and no full regression was repeated. No production source, deployed artifact or security parameter changed. This is extraction infrastructure, not a completed 100-bit proof.
