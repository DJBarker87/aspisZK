# NFZ coverage

**Admitted coverage remains 585/587. The requested repair is incomplete.**

`NFZ_inventory.py` re-derives the raw NDT inventory union, discloses its precise
inherited difference from NFX, applies the empty pinned overlay, and preserves
every NFX row and composed status. `NFZ_slice_build.py` is a prefix-owned copy
of NFQ_build.py's closure core with only input/output routing changed and its
unchanged original-Q/S closure assertions retained. It yields D = 295
functions, 448 internal edges, 343 rows. TX2:046 and TX2:211 remain OPEN and
outside the slices. No row is removed or REACHABILITY-EXCLUDED.

NFX counts remain: CLOSED 167, CLOSED_under_ae 4, QUALIFIED 89, OPEN 331,
total 587. The overlay closes zero rows and changes zero status fields.

For review only, NFZ_HYPOTHETICAL_COVERAGE.json inserts three source-only edges
(the two concrete WideExact callers and first_decoded -> error). On the
**existing 587 rows with original fixed Q/S membership**, this would give
587/587, D = 297 functions, 450 internal edges, 345 rows. This is not admitted
coverage and omits possible new-node expansion.

A material consequence: re-deriving Q from its roots under those edges adds
WideExact::from_m31. NFQ's assertion that original Q membership is unchanged
would fail. A real repair therefore must review Q's expanded membership and
its new call-domain obligations, not merely add both rows to D. The three
new trait-embedding nodes and circle_fallback_point candidate also require
compiler reachability review and explicit inventory occurrences if reached.
Thus a 587/587 existing-row count alone is not an exhaustive repaired-cone claim.

The raw NDT union and current NFX canonical graph differ at the two occurrences
of WideExact::to_le_bytes: NFX lacks the conservative self and M31::to_le_bytes
edges present in the raw inventory union. NFZ_BASELINE_GRAPH_DIFF.json records
the exact inherited delta. NFZ preserves the pinned NFX graph; it does not
introduce those deletions or claim to have re-justified their historical review.
The NFZ overlay itself is additive and currently empty.
