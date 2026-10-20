# S3 `Variant::row` loop body and totality

This source-only packet records two focused Lean checks. The body proof generalizes the extracted continuation to every `d < 5` using the literal TAU lookup. The loop proof uses that body result with `loop.spec_decr_nat` and proves the extracted S2 row function returns successfully for every input.

It does **not** prove that the returned value equals `s2Row`; the accumulator value equation and downstream classification bridge remain open. The proof owners use only standard Lean axioms. No OLean, IR, generated binary, or cache object is included. Exact source/object pins, import hashes, resource limits, and receipts are in `packet.json` and `../evidence/s3-s9-current-repin-20261020/row-loop-body-totality-v25-v4/`.
