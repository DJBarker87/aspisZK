# Changed-source serializer retry

RPz3_543 failed on the raw serializer Funs source b70eb3e1...: it declares
ChunksExactMut.next as the old pair-returning Iterator API, but selected
P6ChunksExactMutModelV3 supplies the triple with a restoration continuation.
Zip.next also has the old structure/API interpretation. Full errors/resources
remain in RPz3_543 and RPz3_frontier.json. Diagnostic sorry is not accepted proof.

The committed sibling sources/generated-adapted/Funs.lean in the same
s5-p6-original-serializer-output-20261020 packet as the already selected
FunsExternal uses P6ToBytes.StdModel.MutableIterator, zipNext and its zip
constructor. This is an existing byte-pinned source selection, not an edit to
any generated file or another worktree. Its hash differs from the failed raw
source. Only this changed source is eligible for a new attempt. The original
failed receipt is preserved; state before the change is RPz3_pre-adapter-state.
No caller premise, source-adoption claim, historical object identity or release
artifact correspondence is inferred from this selection. Top statement and
ledger remain unchanged; no new joint non-vacuity witness.
