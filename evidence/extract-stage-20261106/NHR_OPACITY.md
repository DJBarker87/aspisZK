# Explicit driver opacity

NHR_OPACITY.json lists each call boundary and its reason, per driver. No opaque
callee is certified by making it opaque. In particular Prepared::new,
verify_observed and finish pair/producer completeness remain successor
obligations. Existing packet domains are not weakened.

Inherent methods use Charon's documented NameMatcher grammar:
`crate::verifier::{impl crate::verifier::Prepared}::new`.
NHF's `crate::verifier::Prepared::new` omitted the impl component and did not
match. NHR retains the full LLBC declaration inventory (name, span, opacity,
body kind and source-text hash) and refuses to start Aeneas if a non-root
Aspis function body unexpectedly remains transparent. This checks actual
extraction boundaries instead of assuming command-line intent was respected.

The generated types are included explicitly. The driver remains transparent;
its callees are opaque. Core Option/Result/ok_or remain explicitly included,
with NHA's exact compiler and Aeneas option family. Field arithmetic is not
proved or unfolded here; no Kani is run. Runtime digest values remain trust.

## Corrected matcher validation

E001's Charon succeeded but its inventory collector failed on source_text:null;
Aeneas did not start. Its retained LLBC also confirms explicit inherent impl
patterns DO NOT MATCH this executable. Read-only matcher source inspection shows
`(PatElem::Impl(_pat), PathElem::Impl(ImplElem::Ty(..))) => false // TODO`.
E002 therefore uses `crate::verifier::_::new`, retaining the intended fully
qualified method path separately. The selector's actual matches and source spans
are pinned: Prepared::new is Opaque at verifier.rs72–89. All seven prepare
boundaries pass the inventory check. Synthetic closures, constants and error
conversion remain emitted as part of the driver. E002 exits0 and emits Lean;
this supersedes the initial unvalidated syntax advice above.
