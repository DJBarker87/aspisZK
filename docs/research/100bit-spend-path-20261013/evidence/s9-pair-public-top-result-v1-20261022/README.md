# Pair public helper result

This packet records a green theorem for the selected Pair public helper wrapper. Given a successful Pair call and canonicality of successful mapped input reads, the theorem obtains the same Candidate output through the wrapper map, then reuses the Candidate top total-correctness result to establish canonicality of all four returned cells and the original two-seed S2 coefficient equations. The output and both seeds are tied back to the same Pair call and its `extra` reads.

The contract is explicit: canonicality is required for successful mapped reads of `ap0` and `ap1`, and for successful `extra` reads under the Candidate parser model. The conclusion remains a selected Lean model result; production Rust identity/refinement and the Rust Std/from_fn boundary are not claimed. The packet contains no compiled objects. Run `python3 check_packet.py` to check source, profile, imports, receipt, and axioms.
