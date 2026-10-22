# S4 V10 QueryOps result transport

This packet proves that a successful source-shaped `queryWithOps` run using the V10 candidate literal four-dot callback transfers to a successful run using the original P6 `four_dots` callback, with the same complete query output. The proof inverts the actual query’s first four binds to retain the reached query index, opening, dots result, and continuation suffix. It transports only that successful dots result and reuses the same source suffix; it does not re-prove the arithmetic.

The main theorem is `successful_query_candidate_refines_old_model`. This is a one-way accepted-run refinement in the selected model. It does not establish reverse implication, all-Result equality, Rust Std/runtime correspondence, or whole adaptive-event equivalence. The exact dots callback segment has no hash operations. Production source is unchanged and the candidate is not adopted.

Run `python3 check_packet.py` to verify source, selected direct import source/object pins and producer manifests, receipt, axioms, and absence of compiled objects. The final v12 compile exited 0 in 23.754 seconds. `/usr/bin/time -l` measured process maximum RSS 3,906,682,880 bytes and 0 swaps; aggregate child RSS peaked at 3,892,248,576 bytes.
