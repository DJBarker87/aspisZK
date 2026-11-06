# NKA cuts (in progress)

Target not yet established. 129 allocation-only cut K001 executes the literal heap::uninit continuation after reserve: set_len(1), into_boxed_slice, cast and Box::from_raw, on the identical Claims 1392-byte/align4 request. K002 inverts SAME-address transfer and fails; K003 substitutes a second allocation and fails. No initialized-data or actual allocator outcome claim follows from address identity. Request/segment pin: NKA_HEAP_SITE.json. Actual reserve/error/heap/data/cleanup installation is still OPEN.

NKA_Reservation.rejected/filled compile (L003); NKA_ClaimsModel.parsed (L007) universally quantifies Reservation, derives complete SAME parsed decodes, and retains returning rejection as Allocation. These are model support, not native credit. The existing named Allocator has allocate:A→Nat→Result A and cleanup:A→Result A; no new law is assumed.

NKA_QueryPairs.queries_from_pairs/reached (L010) retain all eight original indices, default state, first stop/advance and finish errors. Source/model support only pending native parent cuts and final gate. 202 remains visible as spurious-by-name under (az)(1); 066/067 are NJT candidates pending ledger17.

No timeout or killed shape repeated. K001/K002/K003 contain no initialized-data property dependent on copying: cap=len=1 before into_boxed_slice; copy mitigation patch is staged unchanged. New outer step uses the exact KMX stub configuration and matched control (pending).
