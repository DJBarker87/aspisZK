# S9 Pair iterator-flow proofs

This source-only packet contains two successful focused Lean targets. The first proves that a successful `pairAfterLow` result is a continuation carrying the same `iterNext`. The second lifts that property through `pairActiveBody` and the extracted source-body adapter. Both theorem axiom reports contain only the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`.

This packet establishes a control-flow fact for the Pair source model. It does not prove Pair-to-candidate arithmetic transport, source-to-binary refinement, or production caller closure. The exact direct import object owners, compile commands, Lean profiles, source hashes, resource receipts, and logs are recorded in the manifest entries. No `.olean` files are included.

Run `python3 check_packet.py` from this directory to verify copied source, receipt, preflight, profile, direct-import hashes, theorem axiom reports, and absence of compiled objects.
