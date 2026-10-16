# Extracted mask to historical semantic declaration

The generic bridge now checks against Lean 4.32: the actual extracted selected-mask
caller returns a canonical value whose field image equals the existing
`R0P.Mask.maskValue` declaration. This is a checked local theorem with
**provisional dependency evidence**, not final source admission or the complete
private-spend theorem. The separate concrete `WideExact` instance now also checks,
with the same provisional dependency qualification.

## Statement and reuse

`AspisR1.ExtractedMaskSemanticBridge.current_selected_mask_maps_to_maskValue`
takes canonical source arrays of 16 claim coefficients and 10 mask coefficients,
one canonical explicit-G value, and 10 canonical point coordinates. It also takes
an explicit field homomorphism from `QM31Exact` into the semantic field and four
equations identifying the images of the source tower basis with `R0P.PackBasis`.

It concludes that the extracted `state_only_selected_mask_value` call succeeds,
its result is canonical, and its decoded field image is `R0P.Mask.maskValue` on
the mapped inputs. Execution success and the desired output equality are
conclusions, not premises. Source and semantic field carriers are not identified
by assertion.

`AspisR1.ExtractedMaskSemanticBridgeConcrete` supplies the actual
`QM31Exact → WideExact` algebra map and reuses the existing
`ConcretePackBasis.basis`. It proves all four basis equations and instantiates
the generic theorem. Its public theorem retains only the canonical source-input
hypotheses; the field map and basis compatibility are no longer caller premises.

The proof reuses the complete extracted-mask formula, the field-hom transport
of the two linear forms, and the historical mask definition. It checks the
16/10 exponent schedules and four-way basis indexing, transports both sums and
the `(1 + L16^26) * g` term, and reorders the additions. It introduces no new
cryptographic assumption or numerical security allowance.

## Exact check

| Item | Recorded result |
|---|---|
| Target | `ExtractedMaskSemanticBridge` |
| Successful attempt | `semantic-bridge-provisional-f` |
| Lean | 4.32.0 |
| Exit status | 0 |
| Wall time | 3.23 s (`time`), 3.263 s (controller) |
| Peak RSS | 4,063,528 KiB |
| Process swaps | 0 |
| Scope | MemoryHigh 4 GiB, MemoryMax 6 GiB, MemorySwapMax 0 |
| Axiom report | `propext`, `Classical.choice`, `Quot.sound` |
| Source SHA-256 | `4659ed545ebfbc0d41f8108c4c7b3f2d2f5816bb1bd5fa979cd53bb6227878d1` |
| Output SHA-256 | `bb280cb39694aef62bbcf0c6dc57d5c92e7a93946f410fea2f16074e616f5152` |

The controller records its retained source base as
`b40d1cfffadbdf967f84cca23ea4e7f1553d564f`; the new target is identified by the
exact source hash above. Its current mask dependencies are committed through
`39cda89cc9e06961684ec5fd0209312b5c15ec29`. The receipt pins the exact imported
objects and environment. Five failed predecessor attempts remain in the archive;
their emitted axiom lines do not count as successful checks.

The concrete target `ExtractedMaskSemanticBridgeConcrete` passes in attempt f:
exit 0, 2.96 s (`time`), 2.996 s (controller), 4,052,352 KiB peak RSS, zero
process swaps, under the same 4/6/0 GiB scope. Its two reports, `basisCompatible`
and `current_selected_mask_maps_to_maskValue`, contain only the three standard
axioms. Source SHA-256 is
`d8284caa37e249240c812eeb4db381d8891715d0e365fe36d4b0b42d16adb1df`;
output SHA-256 is
`7f521e170e90a973ec36df17d92326e70d884c55ebfe3b80c3b000d082c5fbfb`.
The sole change from the reviewed draft is marking the alias of the existing
noncomputable basis as `noncomputable`. The failed import-resolution and
computability attempts a–e are retained separately.

## Why evidence is provisional

The old `R0P.MaskValue` cache object is pinned, but its historical import census
contains missing source-to-output records. Of the original 147 indexed modules,
45 have exact source/success/output binding, 80 have exact-source successful
records plus separately pinned outputs, and 22 have source/output pins without
matching successful records. A focused queue addresses the latter 102. This is
a historical subset, not a claim that the complete project import closure is
already accounted for: additional Wide and external project imports are recorded
separately.

The generic check used the disclosed old cache environment. Subsequent cache
overlays change import resolution, so final admission requires an explicit
dependency reconciliation and a check against the resulting environment. The
provisional object and original receipts are retained, not relabelled as final.

The evidence also retains the focused `ExactTowerFinite` check against the
current exact-tower base and the narrowly scoped runner change that ignores
Lean comments while reading import lines.

## Remaining obligations

Final dependency evidence, accepted-input canonicality and reader correspondence, actual terminal and
ten-round verifier simulation, and the broader extraction, Fiat–Shamir, privacy
and runtime obligations remain open. This result supplies one source-to-model
arithmetic component; it does not establish 100-bit soundness or zero knowledge.

Evidence: [retained bundle](../evidence/current-mask-semantic-bridge-provisional-20261016/README.md).
The [concrete bundle](../evidence/current-mask-concrete-bridge-provisional-20261016/README.md)
also records the Wide/K1 cache overlays and the exact provisional environment.
