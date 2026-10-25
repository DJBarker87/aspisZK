# Actual checkpoint provenance and authentication

`Port11PROV_TX1Reached.accepted` exposes the actual source op3/op4 returns,
zero, op7 return `(Ok p0,g0)`, and op12 return `(Ok a0)` before batch0. It
preserves the complete earlier observation, actual batch0 trace and actual
suffix returning TX1's SAME saved Vec. It is a new source-cut theorem, not an
assumption that a native `Ops` interpretation of the delegated op7 succeeded.

`Port11PROV_WriterReached.accepted` inverts that actual suffix to obtain the
installed op8 writer call with EXACTLY `p0` and its actual final accumulator
`written`. It does not equate `written`, batch0's initial `a0`, and current18's
restored `a`. They refer to different positions and remain separate.

`WriterRoots.root_slices/saved` prove directly from sparse root selectors that
bytes112..144 and144..176 of the actual checkpoint hold p0's raw roots, and
that the saved Vec is1768 bytes. No canonical Prepared/body/model condition
is needed. `CheckpointRoots.accepted` composes these with the actual current18
return on that SAME Vec and the concrete reader's cursor/field theorems.

`CheckpointQueries.query_slice/saved/accepted` prove the analogous raw22-word
array roundtrip: the actual source selectors emit each raw U32's four bytes;
current18's own `QueryReads` reconstruct those SAME values. This uses the
symbolic little-endian roundtrip for U32, not modulo equivalence and not
`BodyMatches`. It concludes `p.queries=p0.queries`. It does not conclude p=p0,
a=a0, accumulator advance, sampled-query provenance, or source experiment
identity. Current18's existing successful-unwrap semantics are explicit.

`Views.node_call/node_bytes` construct all six fixed source slot views as
functions of the actual proof. `Views.folded` uses the actual range,
conversion and existing `TrustedStd.result_unwrap32` semantics to derive the
model folded root. `BatchOne.reached` retains these actual batch1 source calls.
`FirstBoth.accepted` compares both source reads/conversions/unwraps and derives
`folded=folded0`. It then transfers both actual canonical containment clauses
in the SAME first source record. Every duplicate physical call remains.

`Parser.source` uses the existing owned reference parser theorem to derive
canonical parse, proof length, wire, semantic rows and fixed node-view bytes.
The parser's production adoption at delegated op3/op4 is NOT supplied here.
`Parser.length_wire` removes redundant length/wire hypotheses once canonical
parse on the actual bytes is provided.

## Before / after

Before: `Port10AUTH_FirstBoth.accepted` returns actual p0/p and independently
requires, for each containment clause: actual length, wire, that Prepared's
query binding, arbitrary supplied nodeViews, its two stored-root equations,
and its folded-root equation. No authentication conclusion is produced there.

After: `Port11PROV_FirstBoth.accepted` retains the SAME source experiment and
actual witnesses and derives nodeViews, both folded roots, exact current18
query-array preservation, and both current18 stored roots from the writer.
Its two containment clauses require only actual length/wire, p0 query binding
and p0's two stored-root associations. Existing Std/unwrap semantics are
explicit source-helper gates, not new axioms.

After: `Port11PROV_Authenticated.accepted` consumes these contains clauses and
the actual physical batch success results through `Port10AUTH_Installed`,
existing P6 freezing and `Port6AUTH_Recovery.batches` (the same authentication
engine used by `Port6AUTH_Native.authenticated`). It concludes indexed recovery
for every tree kind and all22 positions in the actual first source log.
Only canonical parse on actual bytes, p0's query/root associations, existing
P6, first-log budget/no-hit and root-frame read/target premises remain.
Consistency of the log is derived. No `contains`, `BodyMatches`, abstract
caller `S2CallerFacts`, model Prepared, full-run equality, or authentication
result is supplied as a hypothesis of this new consumer.

This is a new concrete accepted-source authentication statement, not a claim
that all assumptions of the older `Port6AUTH_Query.accepted` or terminal theorem
have been instantiated. No probability law is conditioned on acceptance.
The fixed source Program is independent of H; the native dictionary is only
its pointwise interpretation. No source hash totality was introduced to the
trace/provenance lemmas; the authentication consumer explicitly retains P6's
pre-existing total oracle field, just as Port6AUTH_Native does.
