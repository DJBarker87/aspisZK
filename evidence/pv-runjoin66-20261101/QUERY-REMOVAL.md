# QueryAppend discharge at the native publication consumer

Accepted78014 proves the original, unchanged
PV_RunJoin_PublishProduced60.PV_RunJoin_Link_QueryAppend at opsNative63,
with the actual Produced family, allocator runtime and world. Accepted78015
installs this proof in NativeQueryDischarge66.links and .publication, whose
conclusion is exactly the original native RUNJOIN_PUBLISH_COMPACT input.

Before: NativeOriginalPublication60.complete required all nine Links, including
QueryAppend. After: NativeQueryDischarge66.publication requires Remaining,
the same other eight links; QueryAppend is constructed from source provenance.
No domain, serializer-success, backend-constructor, bound, world-adequacy,
model-witness or capture-success hypothesis was added to that consumer.
The allocator runtime and world remain explicit as in the inherited dictionary.

The source chain recovers both salted constructor equations from the actual
backend build trace, proves C2 preserves C1, produces lane/word and salt bounds,
and derives folded word and salt bounds from actual contextual constructors.
It then consumes NativeQueryPrimitive64's full22-query totality and byte law.

Ledger rows physically removed: none. Exact native publication premise
removed: QueryAppend. No endpoint-wide or non-vacuity credit is claimed.
Skeleton consistency: reduced to non-emptiness; actual Nonempty P and all other
link discharges remain required. The three TrustItems, observer, simulator,
release pins and all fixed Link definitions are unchanged.

The inherited stopping rule permits stopping on a premise removal. This round
stops after this checked consumer installation and its focused axioms audits,
retaining the unspent budget for FinishContext and actual sequential Nonempty P.
