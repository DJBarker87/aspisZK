# From checked specialization algebra to the factor bound

Working parent `9bc0ceee408f432c879ff2239e3ec565dedcd409`.
This records the next proof obligations, not an achieved probability bound.

The newly checked Sylvester consumer permits `R_gamma = c*V^2` with
`V != 0`, `deg V <= m`, and **c may be zero**. Thus, for even global degree
2m and a nonzero fixed-size resultant, degree drops need not be charged
separately: the kernel and count already cover them. If R_gamma is zero,
choose c=0 and V=1. If it is nonzero, the checked polynomial cancellation
lemma supplies V after the nonzero scalar/H guards.

This observation does not apply to an odd-degree R by padding to the next
even degree: padding both polynomial and derivative beyond their actual
degrees can make the global fixed-size resultant identically zero. In the
odd case, preserving the leading X coefficient makes a polynomial square
impossible; leading-coefficient roots still require their explicit charge.

## A simpler decomposition target to investigate

Instead of proving a separately primitive content decomposition, it may
suffice to construct the literal polynomial identity

`D = H^2 * R`, with R squarefree in K[Z][X].

Z-only odd factors may stay in R. They become units over K(Z), and zeros of
R_gamma are allowed by the actual square-specialization theorem. Z-only
even factors stay in H, whose zero-specialization event is bounded using
one fixed nonzero coefficient. This still requires a proof that squarefree
R stays squarefree after localization to K(Z)[X], and a characteristic-aware
separability/nonzero-resultant proof for its positive-X part. Neither is
assumed complete.

For positive even X degree the proposed combined count becomes
`degZ(H) + 4*degZ(R)`; for odd X degree, use the leading-coefficient root
bound plus the H guard. Additive polynomial degrees would give the common
ceiling `4*degZ(D) <= 8*degZ(F)` for a quadratic F. This is a sharpened
**proof target**, not a replacement numerical ledger entry. The existing
conservative 10*degZ(F) proposal was also conditional.

If R has X degree zero, it is a polynomial d(Z). The new nonsquare
discriminant theorem and the checked twist obstruction are relevant, but
the actual factor/fraction-field maps must be instantiated. Both OOD points
then require the fixed obstruction roots with their actual causal sampler
law, not an assumed independent marginal law.

The decomposition must come from the fixed pre-OOD factor. No candidate,
H, R or exceptional coefficient may be chosen retrospectively from gamma.
Factors of Y-degree at least three and the full accepted-extraction event
remain outside this quadratic argument.
