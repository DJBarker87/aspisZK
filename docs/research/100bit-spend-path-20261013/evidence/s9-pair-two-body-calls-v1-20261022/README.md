# Pair two-body call decomposition

This packet records a focused Lean result for the selected Pair helper loop. From a successful loop result, `helper_success_two_body_calls` extracts the two active body calls in source order and the terminal body call, with exact fixed-range iterator transitions. The theorem is conditional on helper-loop success and does not establish arithmetic meaning or totality.

The packet includes the exact Lean source, import profile, preflight record, command, resource receipt, timing record, and `#print axioms` output. Compiled objects are excluded. Run `python3 check_packet.py` to verify source/profile/import pins and the standard-only axiom reports.
