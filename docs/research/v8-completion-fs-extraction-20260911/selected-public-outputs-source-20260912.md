# Selected public-output source polynomials

`SelectedPublicOutputsSourcePolynomial.lean` constructs the remaining eight
digest and two scalar semantic coordinates as chronological source
polynomials. The digest source includes the anchor, nullifier, both output
commitments, twenty append sibling alternatives, `NODE_TWEAK`, next root and
the conditional carry-frontier row. The scalar source covers the selected
asset constraints.

For each coordinate the leaf proves:

- every one-variable slice has degree at most two;
- evaluation follows coordinate replacement;
- every Boolean row equals the literal selected residual; and
- the source-shaped array binding reads the same-index opening.

Together with the previously checked coordinate leaves, this completes the
mathematical source-polynomial inventory for all 95 selected semantic
coordinates. It does not prove equivalence to the packed/factored mutable Rust
loop, an Aeneas translation, whole callback acceptance, payment extraction or
soundness composition.

Focused NUC compile used Lean 4.32.0 commit
`8c9756b28d64dab099da31a4c09229a9e6a2ef35` under a capped 9G/10G no-swap
scope. Exit was 0, wall 12.96 seconds, peak RSS 6,908,728 KiB and swap 0.
Source SHA-256 was
`77e2924f04f1efa48a1bd5e42f8c76a970bca930635af363cd69349720b3b89b`;
OLean SHA-256 was
`b97e07fecbb541aa02a3da11460959c7e981cb236ac031b9ee57444536db39ea`.
Promoted declarations print only `propext`, `Classical.choice` and
`Quot.sound`. Dependency sources were not rebuilt in this focused check.
