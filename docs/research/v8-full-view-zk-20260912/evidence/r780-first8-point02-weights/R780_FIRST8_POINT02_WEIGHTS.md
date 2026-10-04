# R780 first-eight selected point-0/point-2 weights — scratch release assembly

## Scope

This scratch-only package assembles the five focused green modules that establish exact symbolic source-weight expressions at the first eight selected positions: 0–3 and 92–95, for the fixed point-zero and point-two witness inputs. It preserves every same-target attempt in the inherited manifest, including the rejected monolithic shared-helper diagnostic. No Lean target was replayed for this assembly.

## Selected green targets

| run | target | source SHA-256 | exit | wall | peak RSS KiB | swap | source revision |
|---|---|---|---:|---:|---:|---:|---|
| 1791152047372077000-59020a955835 | `AspisV8R19/R780Point02WeightSharedChunk00.lean` | `4e7e718563968465fb88c1933e84e8b2223f55d57b2d432ae227ce8bb9707709` | 0 | 0:02.83 | 3319608 | 0 | `6d978b061bd20c76322494f7f16c9d7bf3ff8f7e` |
| 1791152059413856000-ba00c6c796d0 | `AspisV8R19/R780Point02WeightChunk00P0.lean` | `5c23cee510b48b7df8cdf231407333ba96b7b85d190690ffe552c8ba233b3b01` | 0 | 0:02.45 | 3341604 | 0 | `6d978b061bd20c76322494f7f16c9d7bf3ff8f7e` |
| 1791152078991043000-81fb9c79f1e2 | `AspisV8R19/R780Point02WeightChunk00P2.lean` | `168943c5282788a3727965f59b4141e05a5e2cf3b73903214b2766224d19f651` | 0 | 0:02.39 | 3343328 | 0 | `7ebc65f37bb6aaed8fcec5ad051c5338e81ca81c` |
| 1791152282983094000-abb9005a0a40 | `AspisV8R19/R780Point02WeightChunk01P0.lean` | `0d2550d406f49c10f1079b4886d44e8f8b0b43becd64f375927a5ba4d1998791` | 0 | 0:10.16 | 3519996 | 0 | `3d65fa74ed5dddc85f40acf754c0225d77368af5` |
| 1791152299383324000-cabcd861bad3 | `AspisV8R19/R780Point02WeightChunk01P2.lean` | `790abca6c646180e3b0493882e1efd619a45f9ff25b63ddd4dc6b6ed02f1909d` | 0 | 0:10.94 | 3519600 | 0 | `3d65fa74ed5dddc85f40acf754c0225d77368af5` |

## Axioms

Each selected receipt contains complete `#print axioms` output. Every listed declaration uses only `propext`, `Classical.choice`, and `Quot.sound`.

## Pins and availability

The inherited `manifest.json` records direct import source SHA-256 values (`import_source_sha256_union`) and runner hashes. No direct imported `.olean` SHA-256 values were retained in the focus receipts; this package records that absence rather than reconstructing cache artifacts.

## Boundary

The package proves expression identities for 8 of 343 scheduled positions. It does not establish all-position coverage, a joint matrix rank, native execution, legal-prefix compatibility, callback chronology, oracle laws, privacy, or soundness.

## Rejected diagnostics

All 16 historical attempt records are retained in `manifest.json`, `logs/`, `receipts/`, and `source-snapshots/`. The old monolithic/shared-helper failures remain rejected diagnostics, not selected green evidence.
