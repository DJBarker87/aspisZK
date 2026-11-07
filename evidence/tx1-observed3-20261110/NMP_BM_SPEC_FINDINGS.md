# Emitted-route statement audit (in progress)

Targets remain canonical RSL.TX1_137.RowSpec_137 and RSL.TX1_087.RowSpec_087.
No row root or ledger promotion. No change to frozen files or trust classes.

137 source order: parse; mark0; public_transcript; begin with mutable transcript;
mark1; verify_finish. The begin reply MUST retain the post-transcript on every
returning arm. Marks are no-ops under deployed detail-phases-off even for an
arbitrary observer. Child136 remains exactly the RSL canonical parameter.

087 source order: filled14759; split13831/928 in SAME allocation; semantic
expansion; values expansion; wide_view; observed137; markSemantic; constructor179.
The external scratch must remain unchanged before179, including Rust Err. A
stopped child has only its earlier effects and no invented final scratch/heap.

Allocation audit: filled has a fallible Result mapped to Allocation. Child
allocation prefixes and full outer abort/diverge must not be collapsed to a
post-success allocation. Unlike NMT-S2, these parents introduce no decoder
Option-plus-alloc replacement. Whether CLOSED child representation transports
faithfully supply their full abort observations remains an explicit obligation.

String-clone audit: neither parent contains clone or a ProgramError/String
carrier at its own error-forwarding sites. The semantic/wire Error in137 is
forwarded;087 maps all semantic errors to verifier::Error::Semantic and all
allocation errors to Allocation. NMT-S1 is not inherited as an own-body clone
site. No pure getter law for arbitrary String errors is being assumed.

Own-input clauses:137 publicDom and semanticBytesDom;087 proof length57607,
observerNone, publicDom. Child finishInputDom and179's caller clauses must
be DERIVED at their SAME reached arguments. Prior conditional source-support
lemmas are not an emitted-to-CLOSED child bridge or a complete physical packet.
