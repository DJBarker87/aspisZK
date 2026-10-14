# GRS / circle inverse computability boundary

Read-only source review of the staged inverse modules at worktree base revision `496110fcb2202fc8094191241f067a972071d396`.

## Result

The new inverse chain does **not** select an arbitrary message from the whole message space. `decoded q` is explicitly assembled from coefficient extraction, polynomial operations, and a fixed 512-by-512 change-of-basis matrix. `imageTest` is a proposition that tests whether this reconstructed message re-encodes to `q`; its existential direction uses the reconstructed message as witness. The proofs establish exact left-inverse and image-test statements.

The implementation remains marked `noncomputable` transitively. In particular, the fixed natural-basis matrix inverse is declared with Lean's `Matrix` inverse operator and there is no executable/precomputed inverse-matrix artifact in these files. Thus this review establishes that the inverse is input-independent at the matrix step and avoids whole-message-space choice; it does not establish an executable decoder or runtime bound.

## Definitions and dependencies

- `AspisCircleTensorBinding.naturalCoeffMatrix K m` is the coefficient matrix of the natural line basis (`CircleNaturalBasis.lean:44-48`). Its determinant is proved nonzero by triangularity and nonzero leading coefficients (`:50-65`).
- `AspisCircleTensorBinding.monomialToNatural K m := (naturalCoeffMatrix K m)⁻¹` is explicitly `noncomputable` (`CircleNaturalBasis.lean:67-71`), with `naturalCoeff_mul_monomialToNatural` proving the product identity (`:73-76`). The decoded pair instantiates this fixed matrix at width 512 twice.
- `AspisV5FriCircleEncoderDistance.fractionalLift d p` is a finite sum over `Finset.range (d+1)` (`V5FriCircleEncoderDistance.lean:104-109`). `inverseLift d p := C (((2:K)^d)⁻¹) * fractionalLift d p` is explicitly `noncomputable` (`FractionalLiftInvolution.lean:91-92`); its inverse law is `inverseLift_lift` (`:94-96`). It uses no message-space search.
- `AspisR1.NaturalPairInverse.naturalCoefficients n p := monomialToNatural K n *ᵥ (fun i => p.coeff i)` and `pair p0 p1` interleaves the two coefficient vectors (`NaturalPairInverse.lean:24-38`). Pair recovery is justified by `naturalCoefficients_polynomial`, `initialP0_pair`, `initialP1_pair`, and `pair_bounded` (`:27-66`). The module has a `noncomputable section` (`:20`), inherited from its fixed matrix inverse dependency.
- `AspisR1.CircleNumeratorInverse.decoded q` applies `inverseLift 512` to `evenPart q` and `inverseLift 511` to `oddPart q`, then passes those to `NaturalPairInverse.pair` (`CircleNumeratorInverse.lean:74-76`). The verified round-trip is `decoded_circleNumerator`; `imageTest` and `imageTest_iff` are at `:116-127`. This module is in a `noncomputable section` (`:21`).
- `AspisR1.GRSMessageInverse.inverse q` is only an alias for `CircleNumeratorInverse.decoded q` (`GRSMessageInverse.lean:22-23`). `inverse_messagePolynomial` and `messagePolynomial_inverse_iff` transfer the circle results through `exactCircleGRSPolynomial_eq_released` (`:25-38`). It introduces no additional choice operation.

A source search over these four decoder modules found no occurrence of `Classical.choose`. The `Classical.choice` reported in their Lean axiom audits is consistent with their explicit `noncomputable` dependencies; the audit does not identify any choice over `InitialMessage K`. `imageTest_iff` chooses no new object: forward uses `decoded q` itself, reverse uses the provided witness.

## Source pins

- `AspisFormal/AspisFormal/CircleNaturalBasis.lean`: SHA-256 `c9705066fdda76adbccae72d1e5ddcf3b17e4d0d9de5330ab36f228ea5819d78`
- `AspisFormal/AspisFormal/V5FriCircleEncoderDistance.lean`: SHA-256 `909dc85e736ceb7997a6f7d7d31c600531712c34015a3ab6d33beb2e66b46525`
- `docs/research/100bit-spend-path-20261013/lean/FractionalLiftInvolution.lean`: SHA-256 `dff26393a9876ad629dfeda60b8c29d100ba11c17ca2d7f2bbfc40635887cdfe`
- `docs/research/100bit-spend-path-20261013/lean/NaturalPairInverse.lean`: SHA-256 `e3704153989df8114429a5a7ad19fbb4e098940182cbdd14cff2eeb026624d9c`
- `docs/research/100bit-spend-path-20261013/lean/CircleNumeratorInverse.lean`: SHA-256 `31dc367c6ebc75d9f7ec4099bddc296fc2a347a522001a7dc6fe2fcc1b076ab7`
- `docs/research/100bit-spend-path-20261013/lean/GRSMessageInverse.lean`: SHA-256 `e7dc88c513141321281caacb469b279d67cddaf085752a915504ab81bf71a847`
