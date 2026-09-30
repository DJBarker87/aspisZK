# R161: selected release base arithmetic

Five focused production files compiled: the R156 generated types/core,
R158 bounded word operations, R159 wide addition/subtraction, and R161
multiplication/reduction/inversion.

The selected release M31 addition, subtraction and doubling implement the
exact field operations on canonical inputs. Reduction is correct for every
U64 input, and multiplication is correct for every raw U32 pair, including
the noncanonical fallback. The symbolic one-fold and two-fold bounds handle
the release wrapping arithmetic. This proves equality to the retained checked
multiplication and reduction implementations; it then proves equality of the
entire square loop and inverse execution. Canonical negation and nonzero
inversion return the exact field value; zero inversion keeps the assertion
failure. Namespace equivalence is a conclusion, not an assumed premise.

All arithmetic audits contain only `propext`, `Classical.choice`, `Quot.sound`.
The imported circle sampler also exposes the previously disclosed cached
`core.fmt.Formatter` type dependency. Its correspondence is not yet proved.
The full raw extraction and adapters, exact source pins, complete audits,
metrics and commands are in `evidence/r161-current-base-arithmetic`.

The extraction now contains concrete selected field, circle and transcript
implementations. Only the core prefix is promoted. No external template axiom
is imported. A separate attempt to extract the actual standard-library fold
and vector extension succeeded at extraction but failed during translation at
the generic zero-size/size dispatch in slice iterator fold. That failure is
retained; no replacement axiom or silent standard-library substitution closes
it. The initial core compile shift-literal type error was corrected to the
cached unsigned wrapping-shift API without changing either shift count.

The first remaining proposition is exact selected CM31/QM31 arithmetic and
circle conversion. The circle sampler, full freeze and its standard-library
operations, all ordered hash calls, full-view privacy and soundness remain
open. No full prefix correspondence is asserted. Verifier source and security
parameters are unchanged; the existing 999,790 / 999,532 CU result is retained.
No benchmark or regression suite was rerun.
