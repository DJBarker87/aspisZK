# Do the soundness and privacy theorems rest on one model? Cone intersection, 2026-11-10

Target not yet established. Lead-run, read-only, no host scope. Inputs: the replayed deployed_splitB reachable list (evidence/replay-l187-20261109/final/L187_AX2_splitB/audit/NEP_proof0_AspisR1.TAS_FinalB.deployed_splitB_REACHABLE.txt.xz, 146,370 constants, walker NNM_ProofDriver 46ee271b…) and Stream B's PV_DEPLOYED_TopView4 reachable list (branch codex/pv-ledger-20261108, evidence/pv-inst-20261110/session10/PV_DEPLOYED_TopView4_72692_REACHABLE.txt, 45,592 constants, walker run-thread-audit.py; it contains the whole closure of R1Z.PrivacyR1HeadlineDeployedReal.privacy_headline_deployed plus this week's PV_DEPLOYED_* models and the ProverRwFull extraction from 9c131667ca).

## Result

Shared constants: 24,796, of which 7,462 are outside the Lean/Mathlib/Aeneas base. The shared project-side constants (list in SHARED_PROJECT_CONSTANTS.txt) are the mathematical core and the sampler:

| Namespace | soundness | privacy | shared | what it is |
|---|---:|---:|---:|---|
| R0P | 1699 | 1152 | 1149 | the R0 protocol mathematics: Poseidon constants and rounds, SemDegree/SemSource, digest rows, Mask, Sumcheck, Public, noteCommitment, path/asset laws |
| R0C | 281 | 29 | 29 | R0C.ModuloField: the field |
| AspisR1 | 34366 | 420 | 355 | SpendRelation, the ExtractedQM31Sampler* family, SamplerWord*, RoundPairing, FirstFold, RetainedFieldByteCodec/RetainedExactLimbCodec, InputWitnessCore |
| AspisR1Post25Sampler / Qm31SamplerIndex / GammaCaller | 52/36/57 | 50/36/30 | 50/36/30 | the challenge sampler extraction and its field |
| AspisV8R19 | 628 | 100 | 100 | sampler word distribution/bridges, Q22WordScan, R599CanonicalFieldTuple |
| AspisCircleGroupOrder, AspisV7ExactOneFoldDomains, AspisV5FriInitialCircleEncoderIdentity | 46/57/42 | 44/56/31 | 44/56/31 | circle group order, one-fold domains, FRI initial encoder identity |

Not shared at all (zero overlap):

| Only under soundness | Only under privacy |
|---|---|
| RSL (935): the spend-relation security layer and TAS interfaces | R1Z (4712), R0Z (3404): the privacy protocol model and its R0 base |
| AdapterRw (850), FIq_Native (1735), FIo_Native (570), AspisR1TerminalDecoder (824), AspisR1PublicPreparation (1968), AspisR1QueryGeometryActual (1886), NEW_GeometryActual (1924): the verifier predicate as extracted from the frozen 4bb3b3f source and its gate models | ProverRwFull (2167): the prover extraction, from the unadopted candidate 9c131667ca |
| the R17 table certificates | PV_DEPLOYED_Dictionary/Environment/CircleSource (503), PDict_StatementTypes/Carriers (159), R1J (81), AspisR1ProducerRelease47 (67), R0PoseidonCopy (255): this week's deployed-prover models, statement types and carriers |

R1Z appears in the soundness cone only twice (two constants) and R0Z not at all; RSL, AdapterRw and FIq_Native appear in the privacy cone not at all.

## Answer, in the owner's terms

- **The field, the Poseidon hash, the spend relation and the challenge sampler (the Fiat-Shamir derivation as extracted) are the SAME Lean constants under both theorems** (R0C.ModuloField, R0P.*, AspisR1.SpendRelation, the AspisR1Post25Sampler / Qm31SamplerIndex / GammaCaller / ExtractedQM31Sampler* family).
- **The verifier predicate, the wire format and statement types, and the prover/verifier interaction are DIFFERENT constants.** Soundness reasons about the verifier extracted from 4bb3b3f (AdapterRw, FIq_Native, TerminalDecoder, PublicPreparation, QueryGeometry) through RSL; privacy reasons about R1Z/R0Z with the ProverRwFull extraction from 9c131667ca and PV_DEPLOYED_* models, with its own copies of the field carrier types (PDict_Carriers.aspis_core.field.M31/CM31/QM31) and statement enums.
- **No theorem in either cone relates the two sides**: there is no constant in the intersection that mentions both an RSL/AdapterRw/FIq object and an R1Z/R0Z/ProverRwFull object, so the different constants are neither proved equal nor proved to refine one another. At present they are different and unrelated, connected only through the shared mathematical core above.
- This is a constant-level statement about dependency cones; it says nothing about whether the two verifier models would agree if compared, only that no such comparison exists in the proofs.

## What one pin would require

Pinning both streams to 4bb3b3f means the privacy side's prover extraction (ProverRwFull) and its PV_DEPLOYED_* verifier/environment models are regenerated from the 4bb3b3f crates, and the privacy top is re-proved over them; the shared core (R0P, R0C, the sampler extraction) needs nothing, since it is already common. Whether the privacy model's verifier should then be the soundness gate's verifier (one set of constants) or a separate model proved equal to it is a design choice for Stream B; today it is neither.
