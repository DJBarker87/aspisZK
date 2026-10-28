# Audit dependency repair

The precise 38299 missing import, AspisV8R19.SamplerClosureProductCorrectness, is tracked in this worktree. audit-repair-resolution.json records its full 77-module closure, all h5 source paths/git blobs/SHA256s at entry HEAD, and the EJR/external authorities for its other modules. Twenty project modules are rebuilt privately under h5; the root succeeds in 38922 with standard axioms. External objects were verified against h4/SCOPE before the first compile. No external object was rebuilt or substituted.

A broader preflight for repeating NativeAdmitted21's complete inherited audit finds these modules in none of the permitted source authorities in this worktree:

- R1Z.PV_Src_AdmissionScalar
- R1Z.PV_Src_PortFinalConstants
- R1Z.PV_Src_PortFullRoundCopy
- R1Z.PV_Src_PortInitialConstants
- R1Z.PV_Src_PortInternalConstants
- R1Z.PV_Src_PortInternalRoundCopy
- R1Z.PV_Src_PortParent
- R1Z.PV_Src_PortPermutation
- R1Z.PV_Src_RecordRootClosed
- R1Z.PV_Src_RootFieldMeaning
- R1Z.PV_Src_SourceCompilerRootClosed

The exact resolved/unpinned graph is admission-audit-resolution.json. This is a stop for that audit step only under h4/SCOPE and h5, not a mathematical counterexample or an overall stop. No grep-resolved source, other job's h5 object or different cohort is substituted. The original accepted NativeAdmitted21 axiom evidence38296 and the endpoint audit37099 are reused at their recorded scope; neither is advertised as a fresh coherent closure replay. The final focused audits cover the new universal proof roots and repaired sampler root separately.

Final focused audits (all exit0, swaps0, standard axioms only):

| ID | Target | Host wall (s) | Peak RSS (bytes) | Source revision | Roots |
|---|---|---:|---:|---|---:|
| 38997 | R1Z/PV_RunJoin_PublicBuildAudit22 | 1.66 | 4198416384 | 92c20acf2533e3b2cf13c014273a641cd1cf7655 | 24 |
| 38998 | R1Z/PV_RunJoin_TreeBankAudit22 | 1.58 | 4196573184 | 92c20acf2533e3b2cf13c014273a641cd1cf7655 | 22 |
| 38999 | R1Z/PV_RunJoin_SamplerAudit22 | 1.6 | 3872186368 | 92c20acf2533e3b2cf13c014273a641cd1cf7655 | 10 |
