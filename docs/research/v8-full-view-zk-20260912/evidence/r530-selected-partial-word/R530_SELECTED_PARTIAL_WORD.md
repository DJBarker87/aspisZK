# R530 selected partial-word arithmetic

Final target `AspisR530SelectedPartialWord/R530SelectedPartialWord.lean`, source
SHA-256 `f6cc4817c97f45ec08241ce2fc490f74fecb85d49f27e473331aafd41c527f3f`,
compiled on source revision `924864affb551a525e854cd7233e54bde0926a6a`
with exit 0, wall 0:01.48, peak RSS 3,697,760 KiB, and zero swap. The exact
final source, receipt, raw log, and complete three `#print axioms` outputs are
preserved under `focus-records/`.

For every U64 input, `partialWord x = (x & 0x7fff_ffff).wrapping_add(x >> 31)`
expressed through existing U64 primitives has natural value
`QmCross.partialFold x.val`, is below `5*p+4`, and is congruent to `x.val`
modulo `p`. The proof uses the existing bit-and value theorem, mask value,
31-bit U64 shift theorem, no-overflow first-fold bound, and raw partial-fold
range/congruence theorems. Each complete axiom report contains only `propext`,
`Classical.choice`, and `Quot.sound`.

The two earlier focused failures are retained: `1791056188410317000` records
the scalar-size normalization mismatch and `1791056201161723000` records a
redundant terminal normalization tactic. No unchanged target was rerun.

This is arithmetic only. It does not prove that the actual LLBC builtin
`BinaryOp Shr Wrap` with signed-I32 literal 31 equals this `U64.wrapping_shr
x 31#u32` expression. It does not prove any source loop, array, iterator,
pointer, callback, or verifier correspondence. That builtin-shift source
binding is the first remaining proposition for this isolated partial route.
