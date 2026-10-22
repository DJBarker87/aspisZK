# Prover commitment continuation 33

Requested research pin: 26b922be6. Actual worktree base: e4fa76dc15a45abf8b095f39d7390cfad546b8f5 (D145). Branch: codex/cx-prover-commit33-20261022.
Target not yet established. Work in progress; no endpoint premise removed.

D145 corrects the prior native BTreeMap gate: the standard library is trusted,
not reverified. This continuation checks publication caller logic with an
ordered-list substitute. The sole added TrustedStd field is
`btree_entry_or_insert_with`: a hit retains the map and returns the existing
value without invoking the pure callback; a miss invokes it once, inserts and
returns that value. A boolean invocation trace makes laziness explicit. The
publication callback performs pure field evaluation, not entropy consumption.
No other trusted field is added. This is a named Prop hypothesis, not an axiom.

D143 observable scope: public statement bytes, proof bytes, and answers to
adversary oracle queries. Timing and other side channels are outside the
privacy contract. Internal tables and attempt counts are not published.

## Verification

Pending focused gates. Env J numbering continues after accepted J9043.
Shared source/object replacements are snapshotted in this branch's host
workspace before installation; dependents needed here will be rebuilt.

Stage 1 checkpoint: J9044 accepts the extended TrustedStd interface and its
model consistency witness. J9046 accepts `ProverCommitPublication33`:
`folded_loop_rec`, `folded_decode`, `folded_loop_decode`, `ordered_consumer`,
and `query_answers`. These are universal loop-denotation/map-interface
results, not yet a source-to-experiment instance. `folded_loop_decode`
preserves callback invocation traces, including duplicate hits. The ordered
consumer permits arbitrary salt-stream transitions; the query answer theorem
retains misses and repetitions. J9045 is a rejected projection-rewrite draft.
All successful checks exit 0 with zero swaps and only the standard axioms.
Complete exact fields and source snapshots are in `evidence/prover-commit33-20261022/lean`.

The source-to-denotation identification is being audited separately with
verbatim shipped loop spans in `harness/native-loops.rs`; surrounding pure
callees and the standard-library map are explicit harness substitutes.
No claim about actual encoding arithmetic follows from those substitutes.
No file under crates/ or programs/ has changed at this checkpoint.

## Demonstrated source-image obstruction (item 5)

J9050 proves `ProverCommitPublicImage33.i_not_source_word`,
`no_total_asset_image`, and `no_total_index_image`. This is a mathematical
counterexample to a field-preserving source image on **every model statement**,
not a tool timeout. `PrivacyR1AcctBasis.K` is `WideExact`, not M31.
`R0P.Public K.assetId` can equal the tower element `i`, which is outside the
image of the M31 algebra map. Independently, `nextPairIndex : Nat` can equal
`2^64`, which has no exact u64 representation. The shipped `Public` uses
`M31` public cells and `source.next_pair_index : u64`.

This does not disprove privacy on admitted/source-representable statements,
and does not rule out a non-field-preserving byte projection on unreachable
statements. It does refute the literal universal, field-preserving source-image
interface needed to identify the same public statement. Merely being typed in
K does not prove membership in the source M31 image, nor bound the Nat index.
No invented public-byte error value, truncation, or new admission premise has
been introduced. The existing theorem and security target are retained.

Exact next interface: define a canonical source public image on the admitted
statement carrier, prove all public cells lie in the M31 image and the pair
index is below `2^64`, and prove the actual `Public::public_bytes` returns
`Ok (pubBytes x)` on that image. If the target must quantify over every
unrestricted model statement, specify and justify its behavior for the two
counterexample shapes above; that cannot be a field-preserving image. Changing
the carrier or adding such a premise is not a deletion-only endpoint edit.
The literal item 5 is stopped under common rule 4; no restriction is silently
added to make it true.

J9047 also accepts first-conflict transcript merge transport through the
existing insert-state/previous and ordered-iteration fields. J9049 connects
the extracted sorted lookup to the std graph lookup, retaining an explicit
numeric-sortedness hypothesis. J9051 rebuilds the unchanged adaptive map
program after the TrustedStd source/object replacement. All new statements
have `#print axioms`, accepted checks have no nonstandard axioms, and no
unchanged full regression has been rerun.

The bounded folded single-transition gate passes against the sorted-list
substitute, including an arbitrary pre-existing entry and both lazy hit/miss
paths. Full details and final remaining gate receipts follow at handoff.
