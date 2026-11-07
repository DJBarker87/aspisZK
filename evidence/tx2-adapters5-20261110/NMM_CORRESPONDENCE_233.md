# NMM 233 correspondence

Frozen Rust revision4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. Saved function SHA256 `bf007e40ab0df0f0ff6a4db0f503d1b576157962095897d142bede45428535d9`. The ledger hashes the braced body; see NMM_SOURCE_HASH_INTERPRETATION.json.

`NMM_AccountsTranscription.transcription` is checked model-transcription support. NMM_REVIEWED_TRANSCRIPTIONS.json records the ReviewedTranscription item. Every source line is retained in NMM_LINE_MAP_233.json; the table groups those line records by source order. The lowered Ops body is not a native packet or a fixed release dictionary.

| Saved Rust lines | Source operation | Lean region |
|---|---|---|
| 1–16 | Signature, exact seven-account destructure and length errors | `transcription` |
| 17–31 | Owner, readonly, distinctness and verifier-checkpoint checks | `transcription: initial guards` |
| 32–46 | Master decode and master identity/PDA checks | `transcription: master branch` |
| 47–56 | Release-registry authentication with original master and accounts | `transcription: registry branch` |
| 57–72 | Checkpoint decode, identity and PDA guards | `transcription: checkpoint branch` |
| 73–88 | Lane decode, lane selection and saved-bump PDA guards | `transcription: lane branch` |
| 89–96 | Complete live-snapshot Box payload | `transcription: live snapshot` |
| 97–106 | Return four authenticated owned payloads and account metadata | `transcription: final Ok` |

Under ruling(bl), allocator internals and pure cleanup are outside the obligation. Returned payload values remain complete. Stopped arms carry their ordered event prefix, without invented post-abort heaps. No endpoint, successful child, whole U16 admission or free Ops parameter is promoted into a row root.
