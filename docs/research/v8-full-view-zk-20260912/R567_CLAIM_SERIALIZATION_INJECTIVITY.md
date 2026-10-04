# R567: Claim serialization injectivity

R567 proves injectivity of the selected byte encodings for every input value, with no canonicality restriction:

- Equal `core.num.U32.to_le_bytes` array values imply equal U32 values.
- Equal R144 `cm31Bytes` imply equal CM31 values.
- Equal byte lists `qm31Bytes (R196.toBefore q)` imply equal native current QM31 values.

The U32 proof uses Aeneas’s existing `BitVec.fromLEBytes_toLEBytes` inverse after unfolding the `to_le_bytes` definition and mapping its U8 bytes back to BitVec bytes. The CM31 proof splits its 4-byte limb encodings with `List.append_inj`; the QM31 proof splits the two 8-byte CM31 encodings and then their four U32 limbs. This establishes byte-map injectivity, including malformed/noncanonical field representations.

R144 already proves exact selected writer shape and lengths; R196 proves the current writer equals the R144 writer after the current-to-before representation map. R567 reuses these results. It does not prove that an actual 18-byte mask-claim record is absorbed at a particular source address, or that the selected claim/candidate prefix leaves that address fresh. It makes no random-oracle loss, privacy, or security claim.

## Verification

- Canonical source: `lean/AspisV8R19/R567ClaimSerializationInjectivity.lean`
- Source SHA256: `9c16521c7aa8e45b12debb467825244c102b429cb81f15aa30985b2a15e11dfd`
- Source revision: `6742daddf92657fee803c56f353415b9a882e8ff`
- Target: `AspisV8R19/R567ClaimSerializationInjectivity.lean`
- Exit status: 0
- Wall time: 1.58 s; peak Lean-child RSS: 3,709,552 KiB; swap: 0
- Scope: `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`; Lean `-j1 -M4500`
- Complete axiom outputs for all three theorems: `[propext, Classical.choice, Quot.sound]`
- The successful compile emitted two unused-simp-argument warnings in `cm31_bytes_injective`; the green source is retained without cosmetic changes.
- All nine attempts, their exact source snapshots, complete logs, and receipts are preserved in `evidence/r567-claim-serialization-injectivity/attempts/`.

## Primitive and representation provenance

The pinned NUC Aeneas cached source is under `/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/aeneas-full/backends/lean/`:

- `Aeneas/Std/Scalar/CoreConvertNum.lean`, SHA256 `d7bbeaa3cc7422dcad0a52ffc1904a2d11751717a7b5d820d645404e0bf81eaa`. Its generic scalar little-endian definitions and progress specifications produce exactly the `BitVec.toLEBytes` and `BitVec.fromLEBytes` representations used by the proof.
- `Aeneas/Data/BitVec.lean`, SHA256 `807552f9144bab26232cdedabf4bdd0a5ea52f5634901d20eeae4d9d962749e4`. It contains `BitVec.fromLEBytes_toLEBytes`; the pinned file has no named `toLEBytes` injectivity theorem, so injectivity is obtained by applying the inverse and `BitVec.eq_of_toNat_eq`.

The imported selected Lean sources are pinned by the successful receipt: `AspisR156FullFreeze.FunsCore` SHA256 `5ef8405549c6feff405715a6697ffff9a370610d5dc116fc452a1046fae0c1f2`; `R144BeforeOodBytesBridge` SHA256 `e2d65628c0b3e8f3a836151bf3deec6f729f065be51197da9ed6845c4d605654`; `R196CurrentByteWriter` SHA256 `3df7103bfc86c9e85c17a724ebad9ab5c2561d89971fffe034537df6c5829f5b`.

For orientation, R196’s `toBefore` maps a **current** QM31 into the R136 “before OOD” representation, and `qm_writer_bridge` states current writer equals that older writer applied to `toBefore q`. R165’s separate `toOld` maps a current value into the retained sampler representation: `fromOld_toOld` states `fromOld (toOld x) = x`; `toOld_encode` states the forward mapping for encoded model values. These map directions are recorded explicitly to avoid reading an older-namespace equality backwards. R567’s third theorem states injectivity for the function from current q to `qm31Bytes (toBefore q)`.

The recursive `evidence/r567-claim-serialization-injectivity/SHA256SUMS.json` inventories the canonical file, report, all attempt artifacts, and the reusable primitive provenance note.
