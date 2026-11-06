# NJR certificates — interim

TX2:065 OPEN; no promotion. The reviewed native cut association is P6/D188 option-A reclassification. Native assertions never gain fields from the Lean cut definition. Exact snapshot SHA256 and asserted lines will be indexed in NJR_NATIVE_CERTIFICATES.json after all controls.

| Member/native target | PASS | Matched FAIL | Scope |
|---|---|---|---|
| M03 pending_destination | K004 | K005 destination, K006 payload | One actual Vec.index_mut destination, all selected raw words and full vector metadata/frame; selected weights read window |
| M09 reader_backing | K007 | K008 backing, K009 owned-drop event, K010 payload | SAME immutable bytes, full Reader reply/cursor, exact Err prefix and owned Vec drop; complete successful Vec frame |
| M05 flush_receiver | none | none | K011 timed out, excluded; split into receiver/slot and destination/frame windows |
| M05 flush_receiver_window | K012 | pending | Full arbitrary immutable receiver and selected output slot |
| M04 query_return windows | pending | pending | Supplemental SAME query Result/ownership/payload boundary, not a re-proof of earlier call arguments |

Lean model/caller facts: NJR_FinishWindows gives raw region transport; NJR_FinishPrepared derives Prepared fields from SAME resume; NJR_FinishDomain.reached derives the actual post-query/flush Domain except its explicit raw-history antecedent; NJR_ReservationSites retains every Reservation arm at its named source occurrence; NJR_Cuts and NJR_FlushComposition give full-cell frame/induction; NJR_ReaderCut transcribes only the actual logged backing and prefix. These are local supporting results, not TX2:065 native closure. Every new top theorem prints axioms; failed elaborations are excluded.
