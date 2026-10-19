# Post-25 indexed sampler candidate

Status: **candidate only**. This packet records a focused Aeneas extraction of a proposed indexed implementation of `low_base_p_digits`, plus Lean proofs about that generated candidate. It does not establish equivalence to the deployed production sampler, production adoption, the ordinary/gamma public consumers, or any soundness/probability claim.

The candidate replaces only `low_base_p_digits`: parse the 32-byte block into eight little-endian words, make eight calls to the existing `qm31_div_pass`, retain each full quotient, write each remainder digit, then return the low quotient word. The production body uses `iter_mut().rev()` and writes each quotient limb. An earlier extraction lost that writeback; it is explicitly rejected as source evidence. A systematic name-only LLBC alpha-renaming attempt preserved IDs/signatures/bodies but Aeneas then rejected mutually recursive specialized `Iterator`/`DoubleEndedIterator` methods. The v3 extraction here is therefore of the **candidate Rust body**, not unchanged production Rust.

The focused generated-loop theorem proves that the emitted candidate loop retains the full helper quotient and stores each digit. It proves the eight-pass result equals the existing indexed repeated-pass model. Raw generated sources and separately sanitized compilation copies are pinned. `check-sanitized.py` verifies that the compilation copies differ from the raw Aeneas sources only by removal of Aeneas' generated `maxHeartbeats`/`maxRecDepth` setting and explanatory comment lines. No resource-option overrides remain in the compiled copies.

The next theorem is the outer assembly bridge: the actual extracted `low_base_p_digits` byte loop must be shown to produce the eight little-endian words consumed by the indexed loop, and its returned low quotient word must be tied to `rank / P^8`. Until that is checked, this packet proves only the indexed division loop, not the full candidate function.

All source, import, command, receipt, time, RSS/swap, and axiom metadata is recorded in `manifest.json` and `evidence/`. OLean/IR/executable binaries are deliberately excluded; their hashes and native cache paths remain in the receipts.

The archived unified diff retains its required blank context lines (one space); its exact bytes are hash-pinned. Raw generated files retain tool-emitted settings only as uncompiled evidence; compiled sanitized owners remove those directives.
