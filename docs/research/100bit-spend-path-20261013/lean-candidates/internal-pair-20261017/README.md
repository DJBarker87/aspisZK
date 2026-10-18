# Internal-pair proof candidates — updated 2026-10-18

This checkpoint contains **twelve checked theorem modules, one definitions-only imported dependency, and five unverified proof candidates**. The full seven-input dot, internal-pair caller and 100-bit security result are not established. FieldSum passed on NUC and Mac; the input/chunk/read/reduce-step components passed on NUC; Iterator, ArrayMapStable, callbacks, maps, RemainingAlgebra and OuterSource passed locally with NUC replay pending. All accepted axiom reports are standard-only. PairSource is a source/object-pinned definitions-only dependency of the checked callback/map targets.

The intended consumer is `PoseidonInternalPairExact.source_success`: actual source execution of the three seven-row maps, two seven-input QM31×M31 dot products, and two internal rounds, agreeing with the existing R0P internal-pair model. The dot executes a four-input chunk and a three-input chunk. Candidates reuse maintained decoder/reducer/field facts, actual internal-round correctness and Aeneas iterator specifications. They introduce no axioms or `sorry`; pending claims still need successful focused checks and axiom reports.

`manifest.json` pins frozen sources, imports, status and evidence links. Checked sources are byte-identical to maintained `../../lean` modules. Check changed files topologically under explicit resource caps; do not start a package-wide replay or cold dependency build. Source-owner aliases must match pinned objects.

The five remaining targets are ReduceLoop, OuterStep, SevenOuter, SevenExact and InternalPairExact. Remaining source/runtime correspondence, cryptographic instantiations and privacy obligations are also open.
