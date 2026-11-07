# NMM 217 correspondence

Frozen Rust revision4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. Saved function SHA256 `257f576fb7bb88442064ebf17ef50f3da046fa83302b02357acd2d58d41d6dc2`. The ledger hashes the braced body; see NMM_SOURCE_HASH_INTERPRETATION.json.

`NMM_LaneTranscription.value` is checked model-transcription support. NMM_REVIEWED_TRANSCRIPTIONS.json records the ReviewedTranscription item. Every source line is retained in NMM_LINE_MAP_217.json; the table groups those line records by source order. The lowered Ops body is not a native packet or a fixed release dictionary.

| Saved Rust lines | Source operation | Lean region |
|---|---|---|
| 1–4 | Signature and constant import | `value/sized` |
| 5–17 | Extent and lane header guards | `value length branch / NLK_LaneHeader.sourcePrefix` |
| 18–23 | Master bytes and nonzero guard | `NLK_LaneHeader.sourcePrefix` |
| 24–32 | Tree header guards | `NLK_LaneHeader.sourcePrefix` |
| 33–40 | Sequence decode and capacity guard | `NLK_LaneHeader.sourcePrefix` |
| 41–46 | Root call at exact32 bytes and error mapping | `NLK_LaneDigest.source` |
| 47–59 | Frontier initialization and20 ordered native iterations, rejecting after write | `NLK_LaneLoopSource.run` |
| 60–62 | Terminal zero-sequence root guard | `NKP_LaneCompletion.finish` |
| 63–73 | Complete returned Box payload | `NKP_LaneCarrier.make` |

Under ruling(bl), allocator internals and pure cleanup are outside the obligation. Returned payload values remain complete. Stopped arms carry their ordered event prefix, without invented post-abort heaps. No endpoint, successful child, whole U16 admission or free Ops parameter is promoted into a row root.
