# SelectedIndexedRead independent statement and evidence review

The reviewed source is `SelectedIndexedRead.lean`, SHA-256 `0c44871e4c84fc545381a6df9bb2d8fa23102f4d2af229da2b6600fa56003b35`. Its six statements match the intended scope:

- `readTyped_encoded` assumes the supplied parser accepts the bounded message bytes, then establishes the indexed read result.
- `readTyped_sound` returns the exact indexed-label equality and parser success on the original data. It uses `IndexedMessage.read_sound` and the selected parameter codec's identity encoding.
- The semantic, circle, and opening specializations address indices `row.val`, `25 + row.val`, and `27 + openingRowIndex row`, respectively.
- `label_injective` is limited to indices below 33 and follows from the selected label value theorem.

No statement recovers literal words or establishes table consistency, source refinement, or acceptance.

The evidence bundle was rechecked after packaging: all listed checksum entries pass; the attempt and final source snapshots match the source hash; direct-import source snapshots match the current worktree files; and all five object members match their manifest hashes and sizes. The receipt/log record the green attempt, exit 0, 1.55 s, RSS 3,583,448 KiB, swap 0, and six standard axiom reports. This review is an independent source/evidence check, not a new compile.
