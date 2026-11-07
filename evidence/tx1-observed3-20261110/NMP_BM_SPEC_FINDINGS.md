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

## NMP-BM-S1: canonical137 observer quantification exceeds the130 packet

Ledger24 TX1:130's certificate is explicitly deployed observerNone only;
NHU_Mark.result/frame/effects all instantiate None. Canonical RowSpec_137
quantifies arbitrary obs, because actual deployed r1_semantic.rs75-80 ignores
obs when detail-phases is absent. The source behaviour supports that broader
claim, but installing NHU_Mark.result at an arbitrary observer is not a valid
SAME-domain application. NMP_Install130.silent is presently a source helper;
it must not be represented as the ledger130 root generalized to all obs.
No observerNone clause is silently added to canonical137.

## NMP-BM-S2: constructor179 packet must cover all observations

NHS_PreparedPacket.source is a successful-constructor theorem with explicit
semantic_finish, opening packet, query returned-Ok, rho block and reduction
premises. At reached179, semantic success can follow from the137 reply; query
success is an internal later outcome and cannot be added as an087 own-input
hypothesis. Prior NMP/NHL error/fail/div companions must be composed with the
SAME179 arguments and ordered opening/query prefixes to yield its complete
PreparedNew law. The canonical087 field includes full Rust Result and final g
on every return plus abort prefixes; successful NHS.source alone does not.
This is an installation/coverage obligation, not a reopened ledger assertion
or a change to the canonical target. No arbitrary String error is cloned by
the parents' mapping closures.
