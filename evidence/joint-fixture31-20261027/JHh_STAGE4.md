# Stage 4: standalone SHA field realizations

All six field statements are checked unconditionally in separate small modules. No field failed the per-module memory limit. No combined instance or unconditional SDK assembly was run; that is the separate owner aggregation gate.

| Field | Module | Attempt | Exit | Wall s | RSS KiB | Swap |
|---|---|---|---:|---:|---:|---:|
| checksum | JHh_ChecksumEquation.source | 007 | 0 | 2.975 | 5711920 | 0 |
| publicInput | JHh_PublicEquation.source | 008 | 0 | 2.699 | 5711736 | 0 |
| proof | JHh_ProofEquation.source | 009 | 0 | 3.224 | 6006200 | 0 |
| tree0: Fin157 | JHh_TreeEquation0.source | 097 | 0 | 14.306 | 6087600 | 0 |
| tree1: Fin157 | JHh_TreeEquation1.source | 098 | 0 | 12.944 | 6040184 | 0 |
| tree2: Fin139 | JHh_TreeEquation2.source | 099 | 0 | 11.879 | 5991888 | 0 |

Each printed axiom report is exactly [propext, Classical.choice, Quot.sound]. Full source revisions/hashes, dependency fingerprints and axioms are in the receipts. These are mathematical SHA facts on fixed requests; no syscall/native/ELF refinement is inferred.

The immutable JHe class has453 equations. The new-prefix JHh extension adds proof/public/checksum (456 total), with no output identity or acceptance field. Exact classes: JHh_SHA_CLASS_EXACT.md.
