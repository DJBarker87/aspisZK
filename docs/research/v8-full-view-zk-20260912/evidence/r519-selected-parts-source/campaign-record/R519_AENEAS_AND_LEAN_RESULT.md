# R519 selected `shared_gamma::parts` translation and focused Lean validation

The selected Fun107 dependency closure translated successfully after two narrowly recorded normalization steps: five `Copy(Global31|Global48)` operands became same-type `Const` operands carrying the captured compiler literal; then only the `Global31` and `Global48` groups were omitted from `translated.ordered_decls`. The global declaration rows themselves remain byte-for-byte unchanged. The post-normalization type visitor and independent row scans found no reachable selected global edge or reference to those IDs. Full failure history and limits are in `AENEAS_RESULT.md`, `AENEAS_RESULT_V1.md`, `AENEAS_RESULT_V2.md`, and `R519_GLOBAL_LITERAL_READ_DIAGNOSTIC.md`.

The successful V3 Aeneas run used the pinned R497 binary SHA-256 `85a1037c1d2e675907c4a9c3b0b87e671633f9284775b1be8720f8f208b4086b`, input SHA-256 `984c87c8a20e301e2c10482b8a723d228684236baa29d51fd426bf85c8531cdd`, exit 0, wall 0.28 s, peak RSS 74,096 KiB, swap 0. Its unit was `aspis-r519-parts-v3.service` with 5G/7G/swap0/128-task limits. `translation.json` reports four translated functions: `r91_raw_add`, `M31.add`, `CM31.add`, and selected `shared_gamma.parts`; it exports no globals or traits. All four Aeneas functions are marked `can_fail=true`, preserving the selected field-operation result behavior. The generated declarations and translation metadata are saved in `saved-output-v3/generated/`.

Raw generated Lean hashes:

- `Types.lean`: `5dbf5fa93e1edf16ad8263ce167b4a82af696a93cdd1f18838f2c1e131294ea2`
- `Funs.lean`: `2f4b1bf46a816f2cdf2f3c09f87e7d260b23dd0bf30e9bbad5a618e4964845a4`

The import-only adapter preserves every non-import line exactly. Adapted `Types.lean` SHA-256 is `281a7e5f31bfb1fad36aab0f767c09d527da320c0065c2ad1515479bbfbf0e00`; it imports `Aeneas.Std`, `Aeneas.Tactic.RustAttributes`, and `Aeneas.Data.Discriminant`. Adapted `Funs.lean` SHA-256 is `adc292e401f99d690688676e28ac8cb269fa68e8d28f796f585b3b1223e9cc12`; it imports `Aeneas.Std`, `Aeneas.Tactic.RustAttributes`, and `AspisR519SharedGammaPartsV3.Types`. This matches the existing focused import normalization pattern. No generated function/type body was edited.

The focused Lean 4.32 cached chain was run in separate systemd scopes with `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`, using `-j1 -M4500`:

| Target | Exit | Wall | Peak RSS | Swap | OLean SHA-256 |
|---|---:|---:|---:|---:|---|
| Adapted Types | 0 | 1.06 s | 2,540,672 KiB | 0 | `b481d55003f7580fd6d55b106bc685cb8a61bb59a0e7e5f5b79b57b6139ee645` |
| Adapted Funs | 0 | 1.01 s | 2,535,760 KiB | 0 | `dc6739e53f7c71d36400fa01c97ac05a40e69e4aee47283ed650de72626507fe` |
| Four-function `#print axioms` consumer | 0 | 0.94 s | 2,512,676 KiB | 0 | N/A (audit output only) |

Source revision recorded for these Lean jobs: `924864affb551a525e854cd7233e54bde0926a6a`. The complete command, environment preflight, logs, receipts, and complete `#print axioms` output are under `lean-runs/`; the earlier Types elaboration that only failed because the cache output directory was absent is retained under `lean-runs-write-failure/`.

Each of the four functions reports exactly `[propext, Classical.choice, Quot.sound]`. The generated Lean files contain no explicit `axiom` declarations. No broader compile, package build, full prepare translation, or CU benchmark was run. This is a translated-and-compiled arithmetic leaf, not yet a proof of its correspondence to the original callback or any privacy/security theorem. The source-adequacy boundary for the exact literal-normalization/export-group projection remains explicit.
