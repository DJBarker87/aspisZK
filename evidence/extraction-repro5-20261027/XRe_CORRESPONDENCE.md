# Reference correspondence and remaining binding obligations

These are source/model correspondences to REVIEW and compose, not a claim of
complete P6 certification. Pinned source revision is4bb3b3f51e16b4525f1d10336e2b0bcbbd775387.
XRe_actual_source_map.json hashes verbatim private function bodies; only names
are prefixed. The root reexports actual crate modules, with no stubs/contracts.
Public compact functions are called directly from the pinned dependency.
Owned safe references are XRe_reference.rs; no shipped source is edited.

## prepared_claim

| Release verifier.rs | Owned reference lines | Lean correspondence / missing item |
|---|---|---|
|54 powers7(kappa) |3 |Actual arithmetic model/powers recurrence binding OPEN; K005/006 time out. |
|55 seven zero parts, inactive at0 |4–5 |Seven-part arithmetic representation OPEN. |
|56 six points |6–7,16 |Point enumerates six branches in XRe_Reference; indexing relation OPEN. |
|57 Dot::new |8 |Actual Dot state/count/bounds model OPEN. |
|58 29 gamma entries |9–10,13 |29-entry scratch successful-powers association OPEN. |
|59 six scalar selections |11 |scalar_selection proves projected six-way control only; K004 time out on full carrier. |
|60 push/map_err(Parse)/? |12 |Same source Dot helper, same error branch; full K001 timed out. No stub. |
|62 parts[point+1]=finish |15 |Finish/state/count/arithmetic frame OPEN. |
|64 initial zero claim |18–19 |WideExact field interpretation OPEN. |
|65 seven trace14 events and mul/add |20–24 |Same calls and order in Rust references; no complete Lean arithmetic/effects model. |
|66 trace14 index7 |25 |Preserved in Rust reference; release detail/profiling distinction retained. |
|67 Ok(claim) |26 |No actual full-result association theorem. |

Inputs to the failed whole harness use actual29 entries, six selections, seven
parts,928 y1 bytes and canonical arbitrary scalar/extension limbs. Those
canonicality assumptions are satisfiable (all-zero values); their derivation
from an accepted release run is a remaining obligation. The SemanticTranscript
constructor uses real SHA256, not a digest stub; constructor cost is part of
the failed harness. No successful whole-leaf theorem is inferred.

## checkpoint

| Release verifier.rs | Owned reference lines | Checked/modelled scope |
|---|---|---|
|326 capacity(checkpoint_size) |72–73 |Allocator/capacity/returned Vec carrier association OPEN. |
|328 magic/header/tag/next truncation |74–75 |K015 exact header-stage byte comparison; arbitrary u8 tag and usize next. |
|329 proof digest,public digest,state |76–78 |checkpoint models ordered,state-threaded calls; actual field encodings/heap/effects OPEN. |
|330 two roots |79 |K016 compares all64 positions via arbitrary index. |
|331 four E fields |80 |K002 proves E put bytes and prior one-byte prefix, not heap/capacity effects. |
|332 rho |81 |K003 proves K put bytes and prior one-byte prefix, not heap/capacity effects. |
|333 22 queries |82 |K017 PASSES exact22/u32 stage. |
|334 10 semantic alpha fields |83 |K018 PASSES exact10/K stage. |
|335 two circle points/four K coordinates |84 |Rust sequence retained; no separate terminal Kani proof (budget prioritises expansion repair). |
|336 claim and rhs |85 |E put helper evidence only; enclosing frame OPEN. |
|337 accumulator power |86 |K put helper evidence only. |
|338 weights |87 |K020 exact64/K stage TIMES OUT; other variants256 weights NOT covered. |
|339 checksum(domain,payload) |88 |Third digest invocation is state-threaded in Lean; actual serialized payload association OPEN. |
|340 size assertion and return |89 |Full checksum/bytes/allocator/result association OPEN. |

No whole checkpoint harness is passed. Private-field serialization stages are
verbatim source snippets, with exact values/counts, not a call to the whole
checkpoint function. Kani byte equality does not certify allocation effects,
returned Vec capacity, runtime ownership, source-to-ELF, or rejected prefixes.
Lean checkpoint's `body` parameter deliberately records the UNPROVED payload
projection; its three-call theorem is not full checkpoint equivalence.

## compact::check_values

Release compact.rs loop over chunks_exact16 -> reference28–38 -> Lean chunks16,
canonical4,checkValues. Each u32 little-endian parse/range comparison is explicit
in reference31–33 / Lean le32,canonical. Incomplete suffix ignored in both.
K008 proves every length0..31 and arbitrary bytes; K007 actual y1 bound464 times
out. Lean checkValues_short handles <16; multi-chunk source iteration/carrier
association remains OPEN. No entire semantic scan or enclosing parser closure.

## compact::expand_values

Release compact.rs length/alignment guard -> reference40 -> Lean expandValues.
Source chunks16/32 zip, low-half copy, high-half fill0 -> reference41–46 ->
Lean expandRow/expandRows. K009 at464/928 times out; K010 at32/64 fails assertion
unwinding. K019 changes the proof assertion to arbitrary output index at the
SAME32/64 input/output bounds; K019 PASSES (269 checks,5 unreachable), with same input/output bounds.
Lean proves failure frame and aligned successful output length, not bytes-to-
release association. Rust usize-overflow, iterator/borrow and source-memory
frames beyond the checked bounds remain OPEN. Full semantic row expansion can
exceed the y1 bound and is not inferred from it.

## verifier::echeck

Release verifier.rs39–42 -> reference49–60 -> Lean chunks32/echeckRow/echeck.
Reference reads8 little-endian limbs and rejects>=P or (k and nonzero high).
All actual source errors here map to Parse; the Lean CodecError name is a
reference carrier only, and its release Error transport is OPEN. K013 proves
all lengths0..63, both k values, arbitrary bytes. K011928/K012224 time out.
Full loop/source-carrier composition is not inferred from one-chunk coverage.

## candidate::wide_view

Release candidate.rs76–88 -> reference61–67, preserving same borrowed slices,
S2 tag, checked inactive parse/error, fixed root32 and empty query_bytes.
K014 uses actual57607 proof,13831 semantic and928 y1 lengths and compares
Result/field/borrow pointers and lengths, but times out. No Lean borrow/encoding
model or whole-leaf P6 association is supplied. This remains OPEN in full.

## Lean model status and non-vacuity

XRe_L002 passes all seven printed theorem audits; only propext/Quot.sound or
no axioms. XRe_L001's failed proof and diagnostic sorryAx are REJECTED evidence.
The final source has no proof holes, axioms or resource overrides.
Reference models have concrete inhabitants: empty byte arrays, zero scalars,
and a Unit digest state with any concrete byte-returning operation. This is
local-model satisfiability only. No same-witness joint inhabitant of the actual
Rc10_Top hypotheses is constructed. No top imports a new model or assumes its
unproved carrier correspondence; no soundness premise is removed.
