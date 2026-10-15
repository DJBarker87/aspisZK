# Independent review: literal typed words

Reviewed the published source and evidence bundle without recompiling. The final sources match their manifest hashes and both target snapshots; the attempt records classify `a` as failed and `b` as final, with the failure retained. All `SHA256SUMS` entries validate. The final object archive contains exactly the two declared oleans, with matching member hashes and sizes.

`LiteralTypedWords.word` maps lanes 0–25 through the M31 embedding from the C1 slot, lanes 26–27 through the two QM31 coordinates from C2, and lane 28 through the C1 tail. `word_typed` proves each output lies in the corresponding lane subfield by `mem_fieldRange_self`; `word_recovered_eq` identifies this literal word with the total zero-default `TypedRecoveredWords.word`; `word_eq_zeroC2Word_outside_c2` states that C2 affects only lanes 26 and 27. The successful attempt has three axiom reports, all `[propext, Classical.choice, Quot.sound]`; no `sorryAx` occurs in the successful reports. The failed attempt's log includes failure-related `sorryAx`, retained as historical evidence.

This validates the representation and typing statements in the source. It does not establish byte/source correspondence, causal recovery, or acceptance.
