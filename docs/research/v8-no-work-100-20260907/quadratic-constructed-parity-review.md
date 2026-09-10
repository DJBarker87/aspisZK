# Constructed quadratic parity dichotomy

Research parent: `9bc0ceee408f432c879ff2239e3ec565dedcd409`.

`QuadraticConstructedParity.exists_fixed_parity_dichotomy` is now checked.
For fixed a,b,c in K[Z][X], write D=b²−4ac. Assume D is nonzero and its
X degree is below the characteristic p. The theorem **constructs** fixed
nonzero polynomials H,R with D=H²R and localized squarefree R. It returns
the following actual dichotomy:

1. R has X degree zero (the still-explicit twist branch); or
2. every finite set G of gamma values for which
   `a_gamma*U²+b_gamma*U+c_gamma=0` has some polynomial solution U satisfies
   `|G| <= 4*degZ(D)`.

The existential U may vary arbitrarily with gamma, including being chosen
after alpha. H and R are constructed before quantification over G and U.
The bound does not assume a preselected candidate, recovered tuple, provider
success, exact received word, or a supplied nonzero resultant.

## What is composed rather than assumed

The proof consumes the literal UFD decomposition, localization and both
degree identities. It derives the nonzero fixed-size resultant using the
positive degree/characteristic bound. Even and odd cases use the actual
Sylvester and leading-coefficient arguments. The entire H_gamma=0 class
is charged through a fixed coefficient polynomial. Even-degree R_gamma=0
and degree-drop cases are retained, not excluded by an extra guard.

The intermediate even bound is `degZ(H)+4*degZ(R)`; the odd bound is
`degZ(H)+degZ(R)`. The exact identity `degZ(D)=2*degZ(H)+degZ(R)` yields
the common ceiling. No universal claim about all quadratic roots is made
without the twist alternative: e.g. scalar twists can have many horizontal
roots and require the two-OOD obstruction argument.

## Remaining selected-protocol application

This theorem concerns a fixed polynomial factor, not arbitrary received
words or complete verifier acceptance. The actual factor's coefficient
ordering/root equation, its discriminant nonvanishing and degree bounds,
the constant-parity/two-OOD branch and the fixed factor-family composition
must be connected. Only then may an ideal uniform nonzero gamma count be
divided by `|K|-1` for the relevant event. No numerical global error term
is booked here. Factors of Y-degree at least three, the full resource-bounded
payment extractor, source refinement, FS and privacy remain separate.

## Focused verification

NUC over Tailscale, inherited cached scope parent289d7356, same
MemoryHigh8GiB/MemoryMax10GiB/SwapMax0, Lean `-j1 -M9500`.
Command: `bash run_higher_y_nuc.sh <scope> QuadraticConstructedParity quadratic-constructed-parity-nuc-v1`.
Exit0, wall3.09s, peakRSS6,832,908KiB, zero swaps. Both declarations have
standard-only axiom audits; provenance unchanged.

Source: `de4d38d7193b7215d1eb8f503d792984811cb5be1b1f1ccafddd7a6bf4e0c2c8`.
Olean: `e5f1d821baa93bfe7316bd98b5dc424e8046bdf6d9a0105c02b0a56d50b93447`.
Exact source snapshot, log and import manifest retained. No production,
transcript, proof-body or verifier-operation changes.
