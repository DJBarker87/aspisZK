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
