# S4 candidate-loop field transport

This packet proves the selected-model connection between the concrete V10 candidate QueryOps loop and the old P6 callback model. Each successful candidate query result transports to the old-model query with the exact same output. The generic Stage2 loop refinement carries this across the 10-query and 12-query ranges, and the established field-result theorems then produce witnesses for every index in those ranges.

The field corollaries retain scanner success, ClaimPowers success/canonicality, caller-array identity, and initial cursor facts as explicit premises. The result is scoped to the selected Lean query model and its P6 array boundary. It does not prove independent Rust-runtime or full Standard-library correspondence, enclosing caller completion, or production adoption.

Validation: run `python3 check_packet.py` from this directory. The final focused Lean target used Lean 4.32.0 with `-j1 -M 4400`, under the shared atomic Lean lock.
