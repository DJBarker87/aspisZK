# Sharp source-quadratic obstruction degree

Status: [QuadraticSourceSharp.lean](experiments/QuadraticSourceSharp.lean)
is kernel-checked, with two standard-only axiom audits. The committed
`QuadraticSourceDichotomy.lean` and all dependencies remain unchanged.

The stronger constant-parity branch retains the exact obstruction
`E = (swap H).leadingCoeff` supplied by the checked source theorem.
Thus `deg E ≤ degX H`. The constructed nonzero factorization
`D = H²R` gives the exact identity

`degX D = 2*degX H + degX R`,

and hence `2*deg E ≤ degX D`. In the constant-X branch the last summand
is actually zero; no new choice of E or loss of its actual coefficient
support is needed.

`constant_obstruction_sharp` exposes the exact chosen E, its original
H support bound, the strengthened discriminant budget, and the same
two literal `pointSubstitution` implications. The new
`fixed_source_alternative` constructs H/R from the fixed discriminant
and exports the sharp bound instead of `deg E ≤ degX D`.

The other branch is unchanged: every finite set G of challenges admitting
some polynomial-in-X root of the fixed factor has cardinality at most
`8*trivariateYZWeight curveDegree F`. The branch and E are fixed before
the OOD points, arbitrary answers, challenge set or adaptive candidates.
No decomposition, nonsquare discriminant, candidate-family membership,
or resultant is a caller-supplied premise of the exported alternative.

For family aggregation, a separately proved per-factor bound
`degX D_F ≤ 2*degX F` will allow `deg E_F ≤ degX F`, so the product of
fixed obstructions can use the existing additive factor-X-degree budget
without doubling it. This leaf does not itself prove that degree bridge,
form the factor-family product, or assert a sampling/probability bound.

## Focused evidence

The first and only attempt,
[quadratic-source-sharp-nuc-v1.log](experiments/quadratic-source-sharp-nuc-v1.log),
terminated with Lean exit 0 and successful unchanged-provenance
postflight: 3.21 seconds, 6,841,140 KiB peak RSS, zero swaps, two axiom
audits using only `propext`, `Classical.choice` and `Quot.sound`. There
were no warnings or failed attempts.

The source parent is `be7a1731`. The inherited higher-Y runner and
overlay retain their distinct research cache pin
`289d7356c78a4cd493fe61a54f9548f2a0c11298` and borrowed V7 source pin
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`; no cache was relabeled or
rebuilt. All 841 per-run provenance entries matched before and after.

The Tailscale reservation preflight showed 46,768,590,848 bytes available
RAM and no active user build scope or compiler. The inherited 161,300,480
bytes of host swap use was not caused by this job. Its own scope retained
MemoryHigh 8 GiB, MemoryMax 10 GiB, MemorySwapMax 0, CPU 200%, and Lean
`-j1 -M9500`. Depth 200 and 200,000 heartbeats were not raised. All NUC
transport used `100.108.41.90`; `nuc.local` was only the pinned host-key
alias.

- Source and exact attempt snapshot:
  `ac02e4369bfb118c56887037cc7f73c6887101ed22f3298978804e16c1235ab0`.
- Green olean:
  `ecae9985cef74eb6e3b3bc600e213fa6d0b093eda6dc41b836a7c7b63edb24a1`.
- Per-run manifest:
  `1a52d1273a51926b5bc82691e15f678d414c785aef715f321bee98ea2841fc9f`.
- Runner:
  `5780e61b4d286905ab912bb6ab8e103a20908f78c11bea415db40a5fad110e52`.

The exact source snapshot, log, manifest and compiled output are retained
under `experiments/`. The green source is frozen and the serial compiler
slot released. This sharper algebraic budget alone is not a numerical
security or global extraction theorem.
