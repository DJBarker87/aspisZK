# Internal-pair proof candidates — 2026-10-17

This checkpoint contains **17 unverified proof candidates and one locally checked iterator component**. The full internal-pair caller and 100-bit security result are not established. `PoseidonM31DotChunkIterator` passed its focused macOS check with three standard-only axiom reports; it is byte-identical to the maintained source in `../../lean`, with evidence in `../../evidence/m31-dot-iterator-local-20261017`. NUC replay is pending.

The intended consumer is `PoseidonInternalPairExact.source_success`: actual source execution of the three seven-row maps, two seven-input QM31×M31 dot products, and two internal rounds, agreeing with the existing R0P internal-pair model. The dot executes a four-input chunk and a three-input chunk. The candidates reuse the maintained decoder, reducer, field identities, actual internal-round theorem and Aeneas iterator specifications. They introduce no axioms or `sorry`; the remaining claimed proofs still need successful Lean checks and standard-only axiom reports.

`manifest.json` pins every frozen source, its imports and check status. In the pinned proof workspace, install each file under its module name and check changed targets in import order using one capped `lake env lean` invocation at a time; do not launch a package-wide replay or a cold dependency build. Source-owner aliases must match the pinned existing objects.

Pending checks: the remaining 17 changed targets, their dependent bridges and axiom reports, plus NUC replay. The previous checked source cone is based on revision `47be3705b`. Production Rust and runtime artifacts are unchanged. Full source/runtime correspondence, remaining cryptographic instantiations and privacy obligations remain open beyond this component.
