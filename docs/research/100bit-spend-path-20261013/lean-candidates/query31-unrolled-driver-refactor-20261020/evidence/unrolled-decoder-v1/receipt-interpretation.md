# Receipt interpretation

The Charon and Aeneas receipts are for the unrolled candidate source in this packet. The stage runner verified the `input/source-pins.json` `kit_files` hashes before each phase and copied that exact input into each attempt snapshot. `source-pins.json` pins the modified cut at SHA `1aca7eac3de54d703eb8772c4fea0ecdc2e4e0fd808708626e72aeb5a4d35cbb`.

The runner receipt's `source_revision` text is the generic label inherited from the v5 runner configuration (`same source cut; ...`); it is not an accurate description of the source change. The source hash, `input_classification` (`source-refactor candidate ...`), candidate source pin, and captured command/source snapshot establish the actual input. Preserve this metadata mismatch as an addendum; do not rewrite the receipts.

The LLBC output was validated by the runner (`has_errors == false`) before Aeneas. It is not copied into this source-only packet; its SHA is recorded in both receipts. No `.olean`, object, or executable is included.
