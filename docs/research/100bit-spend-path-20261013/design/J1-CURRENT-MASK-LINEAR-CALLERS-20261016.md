# Current mask linear forms and Horner caller

The actual extracted ten-point reverse loop and its linear-form wrapper now
have checked execution contracts. The wrapper derives its own zero seeds and
range, preserves canonicality and computes the expected scalar combinations.
A separate symbolic moment proof connects the loop model to the exact local
copy of the historical two linear formulas. A kernel bridge to the historical
semantic declaration is still separate.

The Horner caller now derives the prepared constructor, coefficient-26 seed
read, reverse range and polynomial result from the actual calls. Canonical
input linear and all 27 coefficient cells remain explicit premises. The next
source obligation is the two coefficient-population loops and their ideal
polynomial meaning, followed by the complete mask caller.

[Evidence](../evidence/current-mask-linear-callers-20261016/README.md) contains
six green targets, 19 standard-only axiom reports, all 24 attempts and an
independent source/object/premise audit. Peak target RSS is 2,999,948 KiB;
process swaps are zero. Existing field, array and iterator proofs are reused.
The full accepted-verifier, extraction/privacy and runtime/settlement gates
remain open. This checkpoint makes no complete 100-bit claim.
