The prior checked constructor/helper theorem takes an arbitrary constructor
alpha array together with an independent pointwise canonicality premise
`halpha`. It also requires that constructor success, the same helper success,
and canonical-read contracts for the supplied `ap0` and `ap1` arrays.

The new theorem adds success of the parameterized emitted ten-round caller
and requires that the constructor consume the coordinate-preserving map of
that exact caller output. It derives the prior `halpha` premise from the same
caller execution. This is producer composition, not a pure logical weakening
for arbitrary unrelated alpha arrays. No independent per-round, sampler-call,
or initial-constant success/canonicality premise is introduced.

The same constructor success, same helper success and both ap0/ap1 canonical
producer contracts remain explicit. Decode/boundary/comparison/value are
universally quantified operation slots. The source constant is an arbitrary
Result; its success is recovered from that same whole caller run, and its
value need not be canonical for this final-alpha property. This does not assert
that changing the constant preserves acceptance or oracle traces.

The strict checker verifies the emitted caller body against the fresh raw
Aeneas source with only the listed slot substitutions. The source cut retains
an unused appended forwarding entry; the actual caller/callee source bodies
match the pinned current source. This and the new source-pinned numerical
reference replay establish focused source/model facts only. Actual allocator
and primitive/source-runtime correspondence, complete Pair success-to-helper
binding, ap0/ap1 source producers, a coherent release-wide replay and the
100-bit security theorem remain OPEN. No missing source proof is treated as
a cryptographic assumption or hidden in a wrapper structure.
