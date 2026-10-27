# Kani proof-run inventory

All sources and full commands are in the named receipts. No stubs or unverified contracts are used. All20 proof runs are accounted for; K14 is inspection only. A passing local cut is not whole-body closure.

| Run | Harness / source unwind | Outcome | Wall s | RSS KiB | Scope / exclusion |
|---|---|---|---:|---:|---|
| BEl_K01 | leaf_c1; 835 | EXCLUDED (raw exit1) | 0.386706 | 201352 | Kani compiler ICE on Infallible carrier; replaced with unused unit error carrier. |
| BEl_K02 | leaf_c1; 835 | EXCLUDED (raw exit0) | 122.686536 | 1011372 | Incomplete at120s; excluded despite raw exit0/manual summary. Replaced by coordinate leaf cuts. |
| BEl_K03 | leaf_c1_coordinate; 4 | EXCLUDED (raw exit1) | 1.907147 | 281388 | Unwinding/reach-check failures at4; increased to actual byte/compare bound65 and disabled legacy reach checks. |
| BEl_K04 | leaf_c1_coordinate; 65 | EXCLUDED (raw exit1) | 3.051077 | 280576 | Legacy cover reported FAILURE; excluded. Replaced cover by explicit conditional assertion. |
| BEl_K05 | leaf_c1_coordinate; 65 | VERIFIED local cut (raw exit0) | 3.001592 | 272492 | Full leaf grammar coordinate projection. |
| BEl_K06 | leaf_c2_coordinate; 65 | VERIFIED local cut (raw exit0) | 3.088523 | 281312 | Full leaf grammar coordinate projection. |
| BEl_K07 | leaf_folded_coordinate; 65 | VERIFIED local cut (raw exit0) | 3.293270 | 281544 | Full leaf grammar coordinate projection. |
| BEl_K08 | leaf_c1; 835 | EXCLUDED (raw exit0) | 122.402124 | 854272 | Incomplete memcmp/Vec-copy expansion at120s; split to exact one-step scratch/call cuts. |
| BEl_K09 | leaf_step_c1; 65 | VERIFIED local cut (raw exit0) | 31.684724 | 775596 | One reached leaf step, arbitrary scratch/coordinates. |
| BEl_K10 | leaf_step_c2; 65 | VERIFIED local cut (raw exit0) | 34.067746 | 777336 | One reached leaf step, arbitrary scratch/coordinates. |
| BEl_K11 | leaf_step_folded; 65 | VERIFIED local cut (raw exit0) | 33.351083 | 804356 | One reached leaf step, arbitrary scratch/coordinates. |
| BEl_K12 | padding_word; 9 | VERIFIED local cut (raw exit0) | 0.553238 | 161012 | Exactly8-byte zero-word predicate. |
| BEl_K13 | whole_batch_tape_coordinate; 689 | EXCLUDED (raw exit0) | 122.646797 | 5006292 | Incomplete nested arbitrary constructor/key loop; flattened tape and explicit loop bounds in K15. |
| BEl_K14 | CBMC show-loops; N/A | inspection (raw exit0) | 0.353904 | 37336 | Loop IDs/bounds only; no proof run or verification credit. |
| BEl_K15 | whole_batch_tape_coordinate; 33 plus BEl_unwindset.json | EXCLUDED (raw exit0) | 122.444226 | 2006328 | Incomplete symbolic node_count/elimination at120s; split leaf traversal then one-step composition. |
| BEl_K16 | leaf_loop_c1; 33 | EXCLUDED (raw exit0) | 122.132413 | 6482748 | Incomplete whole leaf loop at120s; retained verified K09–11 steps and symbolic controller induction. |
| BEl_K17 | recorder_projection; 65 | EXCLUDED (raw exit0) | 122.285879 | 6515292 | Incomplete dead Vec destructor expansion at120s; K18 ends at observation cut before dead audit-log destruction. |
| BEl_K18 | recorder_projection; 65 | VERIFIED local cut (raw exit0) | 45.219150 | 2775700 | Full Vec recorder versus all Point coordinates at a single leaf cut. |
| BEl_K19 | recorder_entry; 65 | VERIFIED local cut (raw exit0) | 21.632139 | 1102076 | Pending entry visible before actual backend return, one leaf. |
| BEl_K20 | opening_geometry; 33 | EXCLUDED (raw exit0) | 121.199306 | 2608544 | Incomplete symbolic whole-proof byte selector at120s; K21 compares same-allocation slice pointer and extent. |
| BEl_K21 | opening_geometry; 33 | VERIFIED local cut (raw exit0) | 1.093336 | 258576 | Same borrowed proof allocation/offset/extent. |

The chronological tape probes are experimental, excluded whole-body candidates. Their proposed684-call bound is not asserted as a certified full body bound; the source accounting theorem supplies its independent900 bound. The actual adopted loop domains for leaf steps are n10/12, position<12, used≤position; scratch16, digest32, opening832. Padding word uses8bytes; slot capacity≤172 gives≤5504bytes,≤688eight-byte words. Generic induction handles loops; no large concrete kernel normalization.

The full reference/source controller is proved only in its named Lean/P6 denotation. The complete physical certificate and recording of the parent-call contexts remain to be connected before L166 can be removed.
