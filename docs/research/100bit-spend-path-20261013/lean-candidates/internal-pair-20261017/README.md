# Internal-pair proof candidates — 2026-10-17

This checkpoint contains **15 unverified proof candidates and three checked components**: the step-by-four iterator, generic exact-field coordinate-sum bridge, and stable-callback Array.map execution. The full internal-pair caller and 100-bit security result are not established. FieldSum passed on NUC and Mac; Iterator and ArrayMapStable passed locally, with NUC replay pending. All accepted axiom reports are standard-only.

The intended consumer is `PoseidonInternalPairExact.source_success`: actual source execution of the three seven-row maps, two seven-input QM31×M31 dot products, and two internal rounds, agreeing with the existing R0P internal-pair model. The dot executes a four-input chunk and a three-input chunk. The candidates reuse maintained decoder/reducer/field facts, actual internal-round correctness and Aeneas iterator specifications. They introduce no axioms or `sorry`; remaining claims still need successful focused checks and axiom reports.

`manifest.json` pins frozen sources, imports, status and accepted evidence links. Checked sources are byte-identical to maintained `../../lean` modules. In the pinned workspace, check changed files topologically under explicit resource caps; do not start a package-wide replay or cold dependency build. Source-owner aliases must match pinned objects.

Remaining work includes the other 15 targets, dependent bridges, final frozen replay, full source/runtime correspondence, remaining cryptographic instantiations and privacy obligations. Rust source changes integrated separately from the lead follow-up retain their own native-gate evidence and explicit open frontier.
