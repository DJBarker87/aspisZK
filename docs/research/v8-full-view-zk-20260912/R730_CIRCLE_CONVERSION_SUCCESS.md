# R730: Circle conversion success outside CM31

Canonical Lean target: `AspisV8R19/R730CircleConversionSuccess.lean`, SHA-256 `84ffdd463d89305a1e6a9df5130f911ab45ada47306f825216dc471bba0ee690`. Focused run `1791132623993311000` used source revision `7dbe65d748ab2292ecc2a9843b9a0bd9bad01e32`, Lean 4.32, `-j1 -M4500`, `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, and `TasksMax=128`.

The target exited 0 in 0:01.69 with peak Lean-child RSS 3,741,996 KiB and swap 0. Both complete `#print axioms` reports contain only `[propext, Classical.choice, Quot.sound]`.

For an exact-tower parameter, R730 proves that an exact successful return `.ok (.Ok p)` from `secure_ood_circle_point_from_parameter (encode t)` implies `t.im ≠ 0`, by preserving both selected rejection branches: singular and CM31-subfield. For a canonical source `field.QM31` input, it transports that conclusion through the exact encode/decode bridge, retaining the same successful result and canonicality premise.

This proves conversion success is outside CM31. It does not prove an attempt condition, whole sampler or callback chronology, original parameter recovery, source-image premises, oracle law, privacy, or security.

The first remaining proposition is to connect these successful parameter conversions to the parameters actually consumed by the complete three-attempt circle sampler and selected callback; the shared-oracle trace and H1 legal-target proof remain open.
