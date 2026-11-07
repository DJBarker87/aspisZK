# NMP cut map (in progress; no native credit)

Baseline ledger24, ruling (bl), frozen verifier/lock 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387.

| Parent/cut | Existing argument channel | Reply/write treatment | Status |
|---|---|---|---|
| 137 parse 138 | original bytes data pointer into local repr(C) Frame; disjoint sibling Log | arbitrary root offset and 27 independently arbitrary slice ranges, parse Err arbitrary full Error | constructor currently covers input-backed Prefix views; full-type widening and physical provenance review OPEN |
| 137 mark 130, twice | deployed mark body | no-op when detail-phases disabled; no Option<fn> property or callback executed | must verify resolved feature/body identity; not a renamed quarantine |
| 137 public_transcript 131 | LoggedHash data pointer | full state32/row8; original instrumentation pointer retained | generic ghost-erasure obligation OPEN; no child's functional law in stub |
| 137 begin 150 | transcript hash data pointer | arbitrary Challenges; every runtime transcript field overwritten even on Err | full state/row comparison at finish; control skips this havoc |
| 137 verify_finish 136 | transcript hash data pointer | all Verified fields arbitrary, real owned claims Box, any Error | output split by independent field groups; same claims allocation checked |
| 087 allocation/split | pending native harness | allocation internals outside obligation | allocation/split result and source extents remain transcription steps |
| 087 expansions/view | pending native harness | every mutable output byte must be havocked | original 14759 same allocation, 13831/928 split required |
| 087 verify_observed 137 | LoggedHash | reply havocked, independent of 137 closure | not blocked by 136/137 law |
| 087 Prepared::new 179 | LoggedHash and mutable scratch | full returned Prepared and scratch writeback required | caller clauses listed separately |

## (bl)(4) classifications

* Allocator internals: excluded by (bl)(3); no invented fresh-allocator theorem.
* Stopped child: ordered digest/oracle/return-data prefix only, no post-abort heap or cleanup. Native panic arm still needs its explicit case; no native credit yet.
* Drops of proof-local values/claims: outside the obligation unless they write account data or return data, by (bl)(3). Allocation identity on returning claims remains observable in the local ownership check.
* Parser reply constructor currently permits every input-backed source-window view, not every possible Rust slice allocation/extent. This is a literal full-type gap under (bl)(2)(a), NOT closure. Continue independent cuts and Lean work while investigating it; do not silently claim a narrowed domain.
* LoggedHash retains a local ghost pointer even in returned transcripts. Its semantic erasure to the deployed digest carrier and generic instantiation remains an explicit obligation, not a new runtime trust row.
* Native scalar/cell projections must be composed using extensionality over every field; a passing projection is not a complete resource packet.

The prepare expansion generators now have a calibrated fixed-array frame-contract method: whole dst is havocked, one arbitrary post-byte is recorded, source child behavior remains uninterpreted. Native frame contract semantic transport is retained as owner-approved P6/D188 tool-trust reclassification, not removed trust. K070-K085 and NMP_HAVOC_ADMISSION.json contain per-extent controls. Dynamic slice shape is retired after K068 compiler ICE.

## Allocation primitive and representation classifications
087's `filled` stand-in is a fresh14759-byte allocation with explicit zero initialization and recorded n/element-size/value scalar assertions. It is classified as an allocation/initialization transcription primitive under(bl)(3), with std/allocator trust RETAINED. It is NOT claimed to be a generator for every Rust `Result<Vec<u8>, r0::Error>` value: arbitrary lengths, arbitrary existing allocation identities and all r0 error tags are not covered by that stand-in. CLOSED064's exact source law must be installed at the SAME allocation site in Lean; this primitive interpretation and physical producer remain OPEN, not a new trust item or silent full-type credit. The old allocation-rejection pass is a local constant-error relay, not an abort/resource packet.

The 137 runtime transcript fields are free state32 and next_row8, and the H field is the existing local-record channel. Typed field assignment makes no raw padding-byte or arbitrary-H-pointer claim. H/padding/ghost-region erasure is therefore an explicit representation obligation. No model object is identified with the entire ghost-extended Frame allocation by pointer equality alone. Likewise the halo window establishes bytes only; it does not establish ownership, initialization or all immutable input bytes for returning137. The parse-rejection input-byte check does not close the returning input-frame case.

These are literal/carrier gaps classified under(bl)(4). They do not alter the frozen source, security contract or trust inventory, and are not reasons to stop other native or Lean work. No complete parent RowSpec or candidate root is emitted from these partial relations.

K090: actual prepare branch_3 selected correctly, CBMC status139 before any verification check. Fixed-array contract calibration on standalone stack arrays does NOT admit this heap-subwindow/nested-stub context. Exact cause unisolated. Parent use is withdrawn; new prepare shape assigns a full arbitrary typed byte array at both Ok/Err mutation cuts with exact KMX stubs, not a custom copy stub. No cap/time increase or unchanged replay.

K091: CBMC status139 also occurs after removing point contracts; therefore K090 does NOT isolate contracts as the cause. Both contexts remain unadmitted. Next changed shape isolates the allocation/memset path: fresh initialized Box<[u8;14759]> converted to the identical Vec<u8> length/capacity under existing std/allocator trust; explicit full typed-array cut mutations remain. No backend/launcher change or cap/timeout increase.
