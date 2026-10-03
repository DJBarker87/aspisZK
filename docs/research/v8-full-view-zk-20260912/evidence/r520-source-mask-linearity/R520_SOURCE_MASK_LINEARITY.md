# R520 source mask linearity

Final target `AspisR520SourceMaskLinearity/SourceMaskLinearity.lean`, SHA-256
`3142f8c42ca9c2b02a17bd724208502eea72efd631c614c2840f30457edaf26a`, compiled with exit 0, wall 0:01.09, peak RSS
2,299,792 KiB, and swap 0. The exact source,
receipt, raw log, and complete four `#print axioms` outputs are preserved in
`focus-records/aspis-focus-1791055084251769000.*`.

It proves addition, scalar multiplication, arbitrary finite sums, and weighted
finite sums for the existing source-shaped `sourceMaskEvaluate` definition.
The proof uses existing `BalancedTransport.transport_add`, direct finite-sum
distributivity for scalar multiplication, and finite-set induction. It requires
only `[Field F]`; no `NeZero 2`, injectivity, nonzero challenge, or circle
premise is introduced.

The result is pure algebra. It does not establish joint coverage, native
privacy, optimized source execution, or source correspondence.

The four earlier changed-target failures are retained in `focus-records/`; no
unchanged target was rerun.
