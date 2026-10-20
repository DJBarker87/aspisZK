# Lead decision: the frozen R1 verifier (2026-10-20)

Codex job cx-pin (3ab179fc9) ran the combined gate set on research b2727acd3
(adopted compact binary-multiproof format + stage-2 refactor + deployment-id
data slots): default/devnet `.text` byte-identical with the id slots at
offsets 1,470,512 and 1,470,544; stage-2 cone extracts with the pinned
Charon/Aeneas (LLBC identical after normalising the destination filename and
short-name ordering); all standing gates pass (P_R1 8/8, retry loop, D78
simulations, mutations, double spend, strict stack audit); six-fixture CU
within PREREG-PROOF-SIZE-2 item 1 with minimum margins 281 CU (stage 1) and
134 CU (settlement); Pool rebuilt to 121f3e29….

**Decision.** The verifier source at research b2727acd3 (verifier-crate file
hashes, toolchains and ELF pins in
`evidence/freeze-20261020/FREEZE.md`; default verifier ELF dfc2a91a… (1,507,400 bytes), devnet-id build fb2fc048… (same size), stage-2 LLBC f11e40b4…)
is the frozen R1 verifier for the soundness theorem (gap-map step 0,
superseding LEAD-REVIEW-FORMAT-ADOPT-20261020.md and the two amendments).
Every re-pin (S1–S10), the stage-2 refinement (R14), the tx1_finish
extraction (R15), the query bound (R19) and the final CU bound are stated
against this revision. Any later verifier source change reopens all of
them and needs a new freeze decision.

Launched on this freeze: cx-tx1-finish (R15), cx-cu-bound4 (final CU bound,
same method as cu-bound3), cx-devnet3 (deployment with the devnet-id build).

Note: the pin evidence was committed at the repository root (`evidence/freeze-20261020/`); it is to be relocated under `docs/research/100bit-spend-path-20261013/evidence/` once the jobs that cite the root path have landed.
