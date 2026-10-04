# R567 primitive and import pins

This note records exact input files and representation directions. It does not add a source/address theorem.

| File | SHA256 | Relevant contents |
|---|---|---|
| NUC cached Aeneas `Aeneas/Std/Scalar/CoreConvertNum.lean` | `d7bbeaa3cc7422dcad0a52ffc1904a2d11751717a7b5d820d645404e0bf81eaa` | Generic unsigned scalar `to_le_bytes` maps the scalar `BitVec.toLEBytes` through U8 construction; `from_le_bytes` uses `BitVec.fromLEBytes`. Step specs at lines 615–630 expose these exact representations. |
| NUC cached Aeneas `Aeneas/Data/BitVec.lean` | `807552f9144bab26232cdedabf4bdd0a5ea52f5634901d20eeae4d9d962749e4` | `BitVec.fromLEBytes_toLEBytes` at lines 514–518 is the primitive inverse. No named `toLEBytes` injectivity lemma appears in this pinned file. |
| `lean/AspisR156FullFreeze/FunsCore.lean` | `5ef8405549c6feff405715a6697ffff9a370610d5dc116fc452a1046fae0c1f2` | Selected generated M31 writes U32 LE bytes; CM31 writes `a` then `b`; QM31 writes `c0` then `c1`. |
| `lean/AspisV8R19/R144BeforeOodBytesBridge.lean` | `e2d65628c0b3e8f3a836151bf3deec6f729f065be51197da9ed6845c4d605654` | `cm31Bytes` concatenates two U32 encodings; `qm31Bytes` concatenates two CM31 encodings. Exact writer and 8-/16-byte length theorems are already proved. |
| `lean/AspisV8R19/R196CurrentByteWriter.lean` | `3df7103bfc86c9e85c17a724ebad9ab5c2561d89971fffe034537df6c5829f5b` | `toBefore : current QM31 → R136 QM31`; `qm_writer_bridge` points from current writer result to R144 writer on `toBefore q`. |
| `lean/AspisV8R19/R165QuarticExecution.lean` | `9cbbcf134276165b0a9d0593dcda2812c9f203f95c218fa940ccdd9ac3687604` | Separate map `toOld : current QM31 → sampler QM31`; `fromOld_toOld x` is oriented `fromOld (toOld x) = x`. `toOld_encode` is the current-to-old encoding relation. |

R567 concludes injectivity for the current-to-before serialized byte function. It does not connect that byte list to the actual compact mask-claim absorb address or prove the address is fresh in an actual selected prefix.
