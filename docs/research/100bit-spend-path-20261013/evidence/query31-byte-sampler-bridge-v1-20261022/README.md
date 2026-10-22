# Query words to sampler words bridge (v1)

This packet proves that a successful extracted `query_words` call on one 32-byte block returns the exact ordered list of eight 18-bit words used by `AspisV8R19.SamplerWords.words` on `decodeState` of that same block. The proof reuses the retained successful byte-mask theorem, the sampler’s little-endian word bridge, and the model’s state roundtrip; it does not assume a separate byte or decoded-state equality.

The focused Lean target is `AspisR1QueryWordsSamplerBridgeV1.query_words_success_sampler_words18`. It compiled with Lean 4.32.0 at launch source revision `ca305452880cea960cfa25ef9d5b2edc80b30150`, exit 0 in 6.921s, peak aggregate RSS 3268329472 bytes, peak process RSS 3278897152 bytes, and zero swaps. `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` for the mask, rank-word, and final bridge declarations. The object is retained outside the repository at `/tmp/d18-query-words-sampler-bridge-v1/objects/QueryWordsSamplerBridgeV1.olean` with SHA-256 `39ab19936b442118dbc1cde25522ab616cbba83e47b4388f59ffbf8b8aa3525e`.

`dependencies/closure.json` pins the full 5,524-module import resolution performed before compile (zero missing modules), and `direct-import-pins.json` records the selected direct `.olean` owner paths and hashes. No compiled object is included. The source profile and every receipt/log are retained for reproduction.

The result only connects a successful extracted `query_words` return to the sampler word-value representation for that block. It does not establish scanner-chain reachability, query-block source binding, or the full surrounding source/Rust refinement.
