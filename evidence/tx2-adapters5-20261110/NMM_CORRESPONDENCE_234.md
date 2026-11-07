# NMM 234 correspondence

Frozen Rust revision4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. Saved function SHA256 `a66f1b17afcbac22918962d978fb3798dc98b2e324d5a32f6c9d8db402e4cbdb`. The ledger hashes the braced body; see NMM_SOURCE_HASH_INTERPRETATION.json.

`NMM_RegistryTranscription.transcription` is checked model-transcription support. NMM_REVIEWED_TRANSCRIPTIONS.json records the ReviewedTranscription item. Every source line is retained in NMM_LINE_MAP_234.json; the table groups those line records by source order. The lowered Ops body is not a native packet or a fixed release dictionary.

| Saved Rust lines | Source operation | Lean region |
|---|---|---|
| 1–12 | Signature and canonical-bump scope comment | `transcription` |
| 13–20 | Common pool/policy header guards | `transcription: op39/op45/op13/op46` |
| 21–24 | Policy law and registry readonly check | `transcription: op15/OwnedAccount readonly` |
| 25–28 | Exhaustive immutable-deployment branch | `transcription: op14/op41` |
| 29–42 | V2 registry data/decode, first PDA and address guard | `transcription: op33/op38` |
| 43–47 | V2 registry ProgramData PDA | `transcription: second op38` |
| 48–58 | V2 registry field/immutable/paused guards | `transcription: op28/op27` |
| 59–61 | V2 entry readonly/data/decode | `transcription: op34` |
| 62–75 | V2 expected entry PDA and address guard | `transcription: third op38` |
| 76–80 | V2 verifier ProgramData PDA | `transcription: fourth op38` |
| 81–93 | V2 complete entry fields and current-slot status | `transcription: op29` |
| 94–96 | V2 return and branch close | `transcription: V2 Ok` |
| 97–110 | V1 registry data/decode and PDA | `transcription: op31/op38` |
| 111–118 | V1 registry field/immutable/paused guards | `transcription: op26/op25` |
| 119–121 | V1 entry readonly/data/decode | `transcription: op32` |
| 122–135 | V1 expected entry PDA and address guard | `transcription: second V1 op38` |
| 136–147 | V1 entry fields, slot guard and complete Result | `transcription: op30 and final Ok` |

Under ruling(bl), allocator internals and pure cleanup are outside the obligation. Returned payload values remain complete. Stopped arms carry their ordered event prefix, without invented post-abort heaps. No endpoint, successful child, whole U16 admission or free Ops parameter is promoted into a row root.
