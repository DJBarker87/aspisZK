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
