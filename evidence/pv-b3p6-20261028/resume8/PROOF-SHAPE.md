# Continuation inspection and replacement

Resume7 attempt61596 simplified through a deeply nested continuation and reached
the default recursion limit. That proof is not retried; no limit changes.

The emitted public_digest_lanes has four initial digest stages,20 independent
frontier stages, and a final next-root/carry stage. Each field payload is
symbolic. The level tests select either an immutable empty root or the public
frontier at that level; row addresses have fixed block/offset bounds. The final
branch indexes next_frontier only when carry<20.

The replacement factors exact emitted syntax into independent stage definitions,
one named success law per stage, and one named suffix equation per stage.
Suffix equations use tag-level bind associativity only; each later suffix and
the arithmetic/selector callees are locally irreducible. Each suffix success
composes its stage success and the next suffix success without traversing later
continuations. The final bridge is a syntax-factorization equation; it does not
evaluate field payloads or the reference terminal. Projection lemmas cover each
public field read by this stage, plus withdrawal normalization for composition.

The initial flat digest_sequence draft is superseded before compilation by this
suffix route: factoring flat bind chains requires explicit associativity,
whereas suffixes preserve the emitted continuation nesting.

All Rust interpretations remain reclassification within existing tool trust.

## Checked continuation replacement

The full factor equation62361 and isolated raw-entry equations62364–62366
still encounter default recursion through their long equality terms. They are
rejected and excluded from accepted roots. Exact raw-suffix definitions and the
last head equation compile, but do not establish the full factorization.

The checked replacement is62367's `digest_ok_continue8`: a named generic lemma
eliminating exactly one head `Result.ok` bind without simplifier traversal.
`recipient_continue8` and `frontier_continue8` supply the small continuation
stage laws.62368 composes the actual unchanged emitted public digest with only
these named stage/callee laws and head-join applications, with arithmetic,
selector, digest and carry components locally irreducible. All25 independent
stage success laws and all25 staged-suffix success laws also passed; the whole
factor candidates are not needed or imported.62369 checks full semantic_packed
success, and62370 checks the generic RustOk binder rules and field/column laws.
The new permanent CPS generator records this head-only join optimization and
has a --check mode. No whole reference evaluation or limit increase is used.
