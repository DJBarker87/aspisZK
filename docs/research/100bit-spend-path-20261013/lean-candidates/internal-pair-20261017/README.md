# Internal-pair focused proof checkpoint — 2026-10-18

All **17 theorem modules** in this checkpoint passed focused checks; the eighteenth module is a definitions-only imported dependency with recovered success log. The complete seven-input scalar dot and actual internal-pair caller now agree with their existing exact R0P models on canonical inputs. NUC replays and the final frozen manifest remain pending; end-to-end 100-bit security is not established.

`PoseidonM31DotSevenExact.source_success` derives execution, canonical output and the exact ordered QM31×M31 dot product for length seven. `PoseidonInternalPairExact.source_success` composes the three actual seven-row maps, both scalar dot products and both internal rounds. Neither assumes successful intermediate execution or an output-model identity. The dot executes one four-input and one three-input chunk.

The proofs reuse maintained word decoding, exact field algebra, current reducers, actual internal-round correctness and Aeneas iterator specifications. All accepted theorem axiom reports are standard-only. `manifest.json` pins exact sources, imports, checked status and evidence links; checked files are byte-identical to maintained `../../lean` modules. PairSource's recovered receipt discloses that its original exact command was not retained.

The remaining external-linear source proof, full projected caller/canonicality derivations, source/runtime and cryptographic instantiations, and privacy obligations are still open. No runtime artifact or full security theorem is released here.
