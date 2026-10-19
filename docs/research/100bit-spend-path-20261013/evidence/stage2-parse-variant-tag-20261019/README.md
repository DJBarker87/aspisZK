# Actual stage-2 parser variant and tag

PROVED: if the byte-pinned adoption-branch `parse_shape` succeeds, its output is `Variant.S2`, whose actual `Variant.tag` is 2. The theorem uses actual compact-layout constants and preserves the generated parser body under explicit slice-comparison and iterator-any operations. It does not assume the comparators are correct to establish this control-flow fact: every successful branch returns S2.

This is the parser component of R18, not a complete Public.tag/transcript binding theorem. It does not prove the concrete comparator implementation, Merkle acceptance, checkpoint provenance, or stage-2 soundness. Those remain OPEN. No commitment model was edited.

Charon and Aeneas succeeded on source c8ea8dd49c81ab970b9dbee8d8b47718f9beb005. All three focused Lean targets passed at -M4400, under 1 GiB high / 2 GiB max / swap0 scopes. Proof axioms are standard. Generated heartbeat/depth settings are removed from elaborated sources; raw generated files are retained only as extraction pins. No binaries are published. Exact source/import/compiler pins, time, RSS and swap are retained in receipts and preflights.
