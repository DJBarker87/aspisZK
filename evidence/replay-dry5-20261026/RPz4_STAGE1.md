# Stage 1: authoritative module lookup

The actual Rc7_Top launcher is Rc7_002.json in the coherent sound-int2 host workspace. Its complete LEAN_PATH is retained verbatim in RPz4_resolution-full.json. The shorter SInt2-001 path alone is insufficient for this later top. No repository source or theorem changed; Lean attempts 0/1500; Kani 0/0. Resolution below means selected object; source provenance is not inferred from an object basename.

| Module | Selected object | SHA256 |
|---|---|---|
| AspisR1CanonicalDotFinish.Funs | /home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisR1CanonicalDotFinish/Funs.olean | 8a319fb2bc7f4489f14e74ae3f520666aa1670bc6ac273349c70f9390eb2912a |
| AspisR1CircleFallback.RawCircleFallbackOutputBridge | /home/dombarker/project-offloads/codex-cx-s2i-20261023/merged-objects/AspisR1CircleFallback/RawCircleFallbackOutputBridge.olean | 866b31c56e11705a18e5b5fbb20ba458074965c02f7ea6fd088d1e0703e9ed95 |
| AspisR1CircleSampleWrapper.Funs | /home/dombarker/project-offloads/codex-cx-s2i-20261023/merged-objects/AspisR1CircleSampleWrapper/Funs.olean | 7abf97410a440730bfc40ad253cd5d3c2bb01c4a1cd09e4f4bfd89086cd09e9d |
| AspisR1FinishDotReturnedDeltaDecodeV1 | /home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisR1FinishDotReturnedDeltaDecodeV1.olean | 62d96b10783de1548a6c0a71b2aa7a0c18f229ed896180ef13c66da4d5a8021e |
| AspisR1FinishRelationCurrent.Types | /home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisR1FinishRelationCurrent/Types.olean | dc2790f031b33bd70a749bec13b96bf2c3709a7c8f09268785bf1bcb68da95f9 |
| AspisR1SelectedMaskProbe.Funs | /home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisR1SelectedMaskProbe/Funs.olean | 8d2e596692dba2366d0fc6a62ce1047ac3e4a54d8cca320e467d57039460177b |
| AspisR1Stage2Accumulate.Funs | /home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisR1Stage2Accumulate/Funs.olean | d3af6e81c27b7532911a81e70dab82cffb0692f9ad80519e6563e7f6797b000d |
| CompPoly.Bivariate.GuruswamiSudan.CoreCorrectness | /home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPoly/Bivariate/GuruswamiSudan/CoreCorrectness.olean | e5b8333447adade5aadfaea592934568862e9e4cd526454edce378d8fc577615 |
| CompPoly.Bivariate.GuruswamiSudan.Interpolation.Basic | /home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPoly/Bivariate/GuruswamiSudan/Interpolation/Basic.olean | 3de961f543ed4a9a041ec82d07c621e3bc75d97b422eddfa2ab300da4202dd1b |
| CompPoly.Bivariate.GuruswamiSudan.Interpolation.Dense.Correctness | /home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPoly/Bivariate/GuruswamiSudan/Interpolation/Dense/Correctness.olean | bdb12a20bb5018c519a047b0e44478b79805119f1892d56fffc4ca4e8d263b03 |
| CompPoly.Bivariate.ToPoly | /home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPoly/Bivariate/ToPoly.olean | 90eb957c921e2784a62a4022c8103da8b05369029a1b2bf6217f64503088fcde |
| CompPoly.LinearAlgebra.Dense.KernelInPlaceCorrectness | /home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPoly/LinearAlgebra/Dense/KernelInPlaceCorrectness.olean | 49da6f73d4b14e85e39f8d73efc259c2e3a68339bb4eedc4c44cdfebc6fe52d0 |
| CompPoly.LinearAlgebra.Dense.RrefShape | /home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPoly/LinearAlgebra/Dense/RrefShape.olean | 9d1895f02c13ea4a75b8a94953b42509484c9df4c888ecd6e5e4154a476eb3c9 |
| CompPoly.Univariate.DivisionCorrectness | /home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPoly/Univariate/DivisionCorrectness.olean | f06e8a523c50643426c2ec134f0259c9df035e6770290386fb44a54d6392ec18 |
| CompPoly.Univariate.EuclideanAlgorithm | /home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPoly/Univariate/EuclideanAlgorithm.olean | 1003fe48e19545cd686e221790299bb4db46b58616beba2372c896bb78881a95 |
| CompPoly.Univariate.Lagrange | /home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPoly/Univariate/Lagrange.olean | bd421b7df232ec769ae1580e61efc07085879e65a6503f66aee019d143ee44ee |
| CompPoly.Univariate.Raw.Modular | /home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPoly/Univariate/Raw/Modular.olean | 0eb58c34e7cdaa9e3f012f2b2eee7c25dfb1597c7b65bc6a58076be7f4458f1c |
| CompPoly.Univariate.Raw.Proofs | /home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPoly/Univariate/Raw/Proofs.olean | 294600c57d782d0d6f1c4c73a31e3b678a70af7b2a6da37491f95206c1332dc7 |
| CompPoly.Univariate.ToPoly.Degree | /home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPoly/Univariate/ToPoly/Degree.olean | fa5b6ec2a8607e9a2b9ea4fc1848cabcb3f3375e750a3814eafda4bd19728326 |
| CompPoly.Univariate.ToPoly.Equiv | /home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPoly/Univariate/ToPoly/Equiv.olean | 326b34c3879fe6cb31d2a016931e3ce11020b3927a6952f74e9f4d2d84516048 |
| CompPoly.Univariate.ToPoly.Impl | /home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CompPoly/Univariate/ToPoly/Impl.olean | de8d80ce0c37a532becc89512160cb74da0c89af2f3b43e5b6ed28c5edf36d20 |
| CurrentClaimSumModel | /home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CurrentClaimSumModel.olean | e84b5e851e6e0e8353ae194c4484e0a24a9f65b1d498774e58c2f0d7b32810a9 |
| S5QRaw.EbyKPushDecodedProductUpdateV1 | /home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S5QRaw/EbyKPushDecodedProductUpdateV1.olean | a2dadf28307a0963ebb8082af80aba9b11b118320dea9b906f74f42cbcd6084d |

All 23 names resolve to objects under the full actual top path. None has a colocated source. Source provenance and import-closure consistency are the next checks. The first shorter-path inventory is retained as a superseded diagnostic, not as the authoritative selection.

R1NaturalProjection selects coherent objects/R1NaturalProjection.olean, whose retained manifest imports AspisFormal.V5FriNaturalBasisRadix4 and seven tactic/library modules. The previous failing source imports AspisFormal.V5FriConcreteEncoderApplicability instead. This rules out equating the failed file to the coherent selected object by basename; byte-pinned source provenance remains to be established. AeneasMeta resolves in merged-objects and is part of the pinned Aeneas library base; no source failure is inferred from the prior missing-library error.

Before/after Rc7_Top.deployed unchanged. Premises removed/added/changed 0/0/0; ledger T0/P0/G0/C0. No new non-vacuity claim. No release claim.
