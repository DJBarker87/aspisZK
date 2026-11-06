# NJR corrected parent cuts

TX2:065 OPEN; target not yet established. Frozen source 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. NJJ parent footprint corrections required by (aq)(5)(2): M03 actual Vec.index_mut destination; M04 complete query returned ownership/length/payload; M05 SAME immutable receiver/index/full raw cells; M09 SAME Reader backing/bytes and owned failure/drop prefix. New cut sources live only in scratch; NJR_native.patch reconstructs them. Frozen shipped files are untouched.

M03 pending_destination uses one arbitrary raw64 vector and one selected weight window, executes the frozen index_mut assignment and increment, asserts destination=raw base+i, SAME length/capacity/base, and every observed row. This avoids NJJ_K015's timed-out two-vector shape. NJR_K004 PASS; NJR_K005 destination mutation FAIL; NJR_K006 payload mutation FAIL. No full-row numeral reduction.

M04 query_return supplements the retained call-argument cut at its returned Result and the literal destructuring. Full raw and weight cells/metadata/scalars are checked in separate windows; the supplemental packet does not by itself re-prove earlier query arguments. M05 and M09 pending validation. Domains beyond these asserted fields are not silently transcribed.
