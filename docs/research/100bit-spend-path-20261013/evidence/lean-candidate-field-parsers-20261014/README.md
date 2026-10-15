# Candidate field parser Lean evidence

This unsealed bundle records nine focused attempts for the retained candidate parsers and their array, support, canonicality, and checkpoint bridges. Seven targets have successful final attempts; two earlier failed attempts are preserved with hash-matched precompile sources. All seven targets use the source base `6e25cda9d35e52df0980dbcd6744522bd3caaab0`.

The final object archive contains only those seven target objects. Prior M31 objects and the directly imported `SamplerWordRead`, `AspisR72Sampler.Funs`, and Aeneas module objects are kept in separate pinned import archives. Runner, environment, attempt receipts, output/time logs, and source snapshots are included. The checkpoint log contains 12 axiom reports; across all successful attempts there are 38 reports, using only `propext`, `Classical.choice`, and `Quot.sound`.

`generated-input/` contains the pinned candidate Aeneas Types/Funs, translation metadata, and LLBC input. The checker at `../../tools/check-candidate-field-parsers.py` verifies the generated bodies, the exact R259 Option support block, and the LLBC Option tags. This bundle records Lean compilation evidence only; it does not establish Rust compiler correspondence or caller-level parser behavior. Root validation is recorded in `ROOT-VALIDATION.json`; the bundle is sealed at the seven-target scope declared in `source-manifest.json`. The separate `lean-candidate-strict-parser-20261014` extension records byte-order and strict parser bridge targets without expanding this bundle’s audited target count.

The candidate runtime patch remains isolated: the candidate cost gate failed, so no runtime adoption is recorded here.
