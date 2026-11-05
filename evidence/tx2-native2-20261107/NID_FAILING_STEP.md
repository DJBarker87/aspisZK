# Excluded and unresolved steps

L001, L002, L007: inspection commands named constants absent at those namespaces.
No theorem credit; retained outputs identify actual canonical owners.
L004: Array.make membership did not simplify implicitly. Corrected the explicit
list carrier, replayed changed source in L005 (exit0, standard axioms only).
The failed elaboration's sorryAx is excluded; no authored sorry or axiom exists.

K001: before harness compilation, missing cfg(kani) literal path input
 tools/r1-builder-reference/tree.rs. K002: included KMX requires allocator_api.
Both own scratch-input errors, no solver verdict. Fixed by importing the exact
retained cfg(kani) path inputs and cfg_attr(kani,feature(allocator_api)); all
frozen crates/programs remain unchanged outside cfg(kani) scratch instrumentation.
Frozen graph, offline execution and unchanged lock are checked per attempt.

Resume diagnosis: frozen verifier.rs::resume calls Reader.e/Reader.k,
read_checkpoint_semantic_alpha and read_checkpoint_weights. NGV/NGO
parse_record/decode_k refer to semantic record parsing, not these checkpoint
reader calls. Their closure alone is insufficient to instantiate op18. Existing
Port4A/T2Nat checkpoint model laws are relevant; EqOk preserves successful outer
values but is not silently promoted to equality of fail/div or native execution.

K016: negative leaf-tag control reached formatted assert_eq panic machinery;
Kani reported an unsupported placeholder check, so this is NOT selected as a
matched semantic control. Own harness changed to plain Boolean assertions with
literal messages (same predicates, same harness names). K017–052 validate this
corrected source with semantic controls and rename checks. K015 is unselected.

L011: adding the old T2Nat_ReaderJoin import collided with canonical
RPz7_ExtractedDigest32Transcript. Removed the unnecessary import; the already
selected scalar/raw/weight objects in NHV's coherent closure suffice. L012 passes
with standard axioms. No shared objects or proved sources were overwritten.
L013–017: incremental sequential-reader proof elaboration fixes (let-pattern
normalization / explicit inner Result constructor types); failed elaborations
and their sorryAx placeholders are excluded. Every submitted source is retained.

K062: actual Reader.raw::<32> on arbitrary1768 backing / arbitrary valid offset
TIMEOUT90s. No credit. K063 onward replaces this shape by seven disjoint offset
partitions of width256, still arbitrary original1768 bytes and selected32-byte
read. NID_RawOffsetCover.cover/unique proves complete coverage of all valid
0..1736 starts; no buffer is fixed, narrowed or replaced. Neither the timeout nor
its unlaunched control/rename shape is resubmitted unchanged. Caps unchanged.

L023: offset variable used Lean's reserved `at` token; fixed to `offset`.
L026: dependent alpha index needed an explicit actual Array length bound; L027
adds that bound and passes. No theorem statement was weakened. L028 raw-row
window composition passes. L018's initial reads transport needed explicit
let-pattern normalization; L019 passes the corrected full Result statement.

K093: actual Reader.k selected value at arbitrary1768 offset / arbitrary limb
TIMEOUT90s. No unchanged rerun. K094–105 replaces it by four fixed limb windows
on the actual resume K-read schedule (rho304, or408+16*row with row<83).
NID_KOffsetCover proves every semantic/coordinate/power/weight call-site offset
is included and bounded. Result K090–092 already covers all valid offsets.
This narrower native value domain is not claimed for other Reader.k callers.

K106: insufficient unwind8 in Kani's fixture constructor for the arbitrary
64-row raw array; failed core::array::try_from_fn_erased unwinding assertion,
not the payload property and not a matched semantic control. Same harness names
and assertions retained, fixture unwind corrected to258 (the retained NHV
64-row constructor bound). K107–118 all pass/control-fail/rename-pass. No timeout
or memory cap changed; K106 was neither timed out nor memory-killed.

K119/K120: actual Reader.e's full inner Result classification on arbitrary
checkpoint1768 and every valid32-byte offset passes with a matched literal
Boolean corruption control. This ordinary Reader helper has no Observer or
function-pointer parameter; no (ae)/(al) specialization is used or inferred.
Its complete native value/caller association is still part of the resume gap.

L047: KMX composition proof completed its all64 equality by rewriting; a trailing
rfl produced "No goals to be solved". Removed that redundant tactic only; L048
passes all five top theorems with standard axioms.

Initial final audit L033–046 (48 roots) passed, but coverage review identified
that the new raw-frame composition should explicitly use prescribed KMX value
laws. NID_KmxComposition adds that source/proof link. Expanded combined import
L049 and following audit are new-source evidence, not an unchanged full replay.
Initial scan/child metrics/raw dumps are retained under NID_initial_audit.
