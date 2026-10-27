# Rejected unrestricted index-bound lemma

L033/L034 did not establish the proposed unrestricted validation error-index
lemma. Inspection of pinned Aeneas Scalar/Core.lean:366–369 shows
UScalar.cMax .Usize is the conservative U32 maximum, while Usize.max is the
platform maximum. The attempted Usize.max≤cMax is false on a64-bit platform.
No bound is inferred from those failed diagnostics, and no leaf model is edited.

The replacement is explicitly restricted to the ACTUAL largest semantic record
payload3712bytes (116*32). Then each error index is below116, so the existing
model's portable-constructor guard cannot fail. The extra bound is local to
this helper and is not a new assumption or discharge at ARX_Root.deployed.
The generic model may panic for non-release giant Slice carriers; no general
native/model claim is made for them. This is a model-domain observation, not a
claim of a shipped Rust bug or a new security assumption.
