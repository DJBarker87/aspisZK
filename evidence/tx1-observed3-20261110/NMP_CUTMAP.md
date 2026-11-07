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
