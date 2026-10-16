# Exact mask basis and power chain

The actual selected-mask `mask_power_26` function now has a checked exact-field
contract: every canonical input produces a canonical result equal to its
26th power. The proof composes the extracted four-square/two-multiply chain,
using retained modular identities and the exact-tower square theorem.

The source tower-basis helper also has an exact-field interpretation for all
four admitted coordinates, in addition to its earlier word/canonicality
contract. The factors are `1`, `i`, `u`, and `i*u`, in the source coordinate
order. Input canonicality and coordinate<4 remain explicit. Small component
identities in the exact carrier avoid treating representation aliases as an
unproved field map.

The Horner model's degree-26 polynomial formula is checked as well. A symbolic
identity for arbitrary n is instantiated at 26, avoiding concrete finite-sum
or field-power normalization. It is connected to the model used in the actual
extracted-loop theorem; the caller setup and array population remain separate.

[Evidence](../evidence/current-mask-power-basis-20261016/README.md) covers eight
successful focused targets, twenty-one standard-only axiom reports, exact
source/import/object pins, retained failures and resource records. Maximum
target RSS is 2,998,648 KiB and process swaps are zero. No production Rust
changed. Complete mask, accepted-verifier, compiler/extraction, privacy and
runtime/settlement obligations remain open; this is not a complete 100-bit
spend theorem.
