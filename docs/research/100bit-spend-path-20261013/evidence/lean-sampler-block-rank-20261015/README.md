# Sampler block-rank bridge

This focused bundle records `AspisR1.SamplerBlockRank.word_numeral_eq_rank`: the reversed eight-word base-2^32 numeral equals the existing 32-byte little-endian positional `blockRank` value. The proof expands only the finite eight-word/32-byte symbolic sums, normalizes their `Fin` indices, then compares the resulting symbolic byte coefficients.

Attempt a is the retained failed proof attempt; its log emits one `#print axioms` report containing `sorryAx` (recorded as a failed attempt, not as a successful audit). Attempt b is the final successful focused compile. Attempt b exited 0 in 1.59 s, peak RSS 2,492,828 KiB, swap 0, under the pinned 4G/6G/0/128 cgroup. Its one `#print axioms` report lists only `propext`, `Classical.choice`, and `Quot.sound`.

This is a mathematical identity among the existing Lean sampler-word and block-rank definitions. It does not prove that the Rust sampler execution refines those definitions or establish a probability law.

Failed-attempt axiom reports are counted as emitted provenance. They are not counted as successful-target audits; only exit-0 final attempts support the successful audit summary. Attempt a emitted one report containing `sorryAx` and remains failed.
