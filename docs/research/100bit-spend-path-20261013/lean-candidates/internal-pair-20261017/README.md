# Internal-pair proof candidates — 2026-10-17

These are **unverified proof candidates**, checkpointed while capped NUC capacity is occupied and a compatible local import cache is being assembled. They are not admitted proof results and do not establish 100-bit security. No successful compilation of these changed targets is claimed in this checkpoint.

The intended consumer is `PoseidonInternalPairExact.source_success`: actual source execution of the three seven-row maps, two seven-input QM31×M31 dot products, and two internal rounds, agreeing with the existing R0P internal-pair model. The dot executes a four-input chunk and a three-input chunk. The candidate reuses the maintained decoder, reducer, field identities, actual internal-round theorem and Aeneas iterator specifications. It introduces no axioms or `sorry`; only successful Lean checks and standard-only axiom reports can validate those assertions.

`manifest.json` pins every frozen source and its imports. In the pinned proof workspace, install each file under its module name and check changed targets in import order using one capped `lake env lean` invocation at a time; do not launch a package-wide replay or a cold dependency build. The currently queued exact sources are `/tmp/<module>-vN.lean` on the development machine and NUC. The maintained source cone is `../../lean`; source-owner aliases must match the pinned existing objects.

Pending checks: all 18 changed targets, their dependent bridges and axiom reports. Existing release evidence remains at base revision `1c058a9f8a7d87e7181e1583119835b880c824bf`. Production Rust and runtime artifacts are unchanged by this checkpoint.

Even if this caller theorem checks, full source/runtime correspondence, the remaining cryptographic instantiations and privacy obligations still require completion before the requested end-to-end security result can be claimed.
