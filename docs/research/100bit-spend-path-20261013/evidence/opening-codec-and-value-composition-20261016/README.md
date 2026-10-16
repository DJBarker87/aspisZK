# Opening codec and value-family packing composition

CanonicalLiteralChunkFacts is a pure Aeneas list/chunk leaf. Its fixed-width partition and seven-chunk facts reuse the mathematical structure of the existing RecordPayloadPartition proof without importing unrelated generated parser instances. It has six checked standard-axiom reports.

CanonicalLiteralEcheckStrictSecondChunkFacts2 composes successful actual generated echeck_round1 of a 224-byte input with ordered canonical WideExact parses and the retained strict logical second-opening codec. The root bytes are explicit input; View::parse section/root identity and transcript framing remain separate caller obligations. The actual echeck extraction and its explicit Option.ok_or library-model boundary are retained in the earlier source archive.

ValueLanePackedComposition composes the two actual add_preweighted calls at scalar offsets 49 (33 cells) and 82 (two cells). The theorem proves source success, output canonicality and every decoded output packed cell. Their contributions are added before packing, including the shared group20. This consumes the already checked complete packed-interval primitive; it does not assume that either source call succeeded. Source construction of the input residual arrays and identification with the full retained valueFamily remain subsequent obligations.

All targets passed focused Lean4.32 checks on the NUC, with exact source/import pins and zero process swaps. Only propext, Classical.choice and Quot.sound occur in printed axiom reports. These are source/codec proof components, not a completed soundness, extraction, privacy or runtime-release theorem.

| Target | Wall seconds | Peak RSS KiB | Axiom reports |
|---|---:|---:|---:|
| `ValueLanePackedComposition` | 2.005 | 4063680 | 2 |
| `CanonicalLiteralChunkFacts` | 1.206 | 2635600 | 6 |
| `CanonicalLiteralEcheckStrictSecondChunkFacts2` | 2.258 | 4119396 | 3 |
