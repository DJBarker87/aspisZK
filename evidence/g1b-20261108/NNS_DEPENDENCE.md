# Stage 1: library dependence before proofs

Source revision: 09ef4e3f4b3; ledger29 rev4 closure. The required top field is
not established. This inventory is written before NNS proof sources.

## Actual 064 call sites (stage 0 source inspection)

* NMX_R9_StageTwo.stage2, lines 15–20, selects NMX_R9_Live241.observation
  in the represented branch; that is Classical.choose of whole native liveness
  (NMX_R9_Live241 lines 65–81), not a function calling NNH_064Install.f064.
* NMX_R9_Native241.meaning, lines 16–21, installs
  NMX_R9_Children241.original; its original/grouped inherit the 064 child
  (NMX_R9_Children241 lines 12–16; NMX_R8_Children241 lines 17–31).
  That child is NMX_R7_VerifierSource241.meaning, defined as Spec.map raw
  LIBB_ObservationModel.law (NMX_R7_VerifierSource241 lines 16–17).
* The unrepresented branch is NMX_R7_Port241.stage2, whose afterPublic
  calls NMX_R7_Verify241.verify (NMX_R7_Port241 lines 24–29).
  Verify241 lines 14–18 select LIBB_Tx2EnvTrace.observation for fitting inputs.
* NNH_064Install.f064, lines 17–23, instead calls NNH_064Execute.observation
  (computed records/outcome/trace, NNH_064Execute lines 8–28).
  Neither stage2 branch mentions that constant.

## Direct canonical uses and their downstream consumers

| Lemma/definition | Source lines | Dependence and required replacement |
|---|---|---|
| NMX_R7_Verify241.packet | 20–25 | Membership in canonical tx2auth from contains_graph; to use a different w requires Refines064 for THIS selected graph |
| NMX_R7_VerifierSource241.full | 25–34 | Whole source relation transported through LIBB_Tx2Auth.same; changing w requires transport of EVERY admitted child observation, not merely one function |
| NMX_R7_Fold241.fold | 11–20 | Fixes V0, consumes Verify241.packet and NMX_R6_Validation.root; generic NMS_R2Fold241 already takes arbitrary V, VerifyPacket and RowSpec242 |
| NMX_R7_Port241.error_member | 67–71 | V0 error carrier/debug only; unchanged by TAS.lib |
| NMX_R7_PortLaw241.public_member/reads_member/after_member/replay_member/canonical | 9–91 | Canonical V and selected verify throughout; membership lemmas are structurally reusable after the SAME verify packet is supplied |
| NMX_R8_VerifierUse241.full | 14–29 | Canonical tx2auth via VerifierSource241.full; all source observations, with error callback/debug preserved |
| NMX_R8_RelReplay241.verify/replay/fold | 12–35 | verify IS canonical tx2auth; fold uses reflexive RelPacket and directly consumes canonical 242 root twice |
| NMX_R8_Encoded241.full | 12–36 | Invokes canonical VerifierUse241.full after SAME encoder and slice |
| NMX_R8_Reads241.full | 13–35 | Invokes Encoded241.full; fixes canonical afterReads |
| NMX_R8_After241.full | 13–31 | Invokes Reads241.full; fixes canonical afterValidate |
| NMX_R8_ValidateUse241.full / NMX_R8_Head241.full / NMX_R8_Native241.full | respective module | Canonical R8 replay transitively; superseded selected242 path retained as support only |
| NMX_R9_RelReplay241.fold | 20–27 | Canonical full242 relation, reflexive canonical064 RelPacket; scanner success and D2 remain generic |
| NMX_R9_ValidateUse241.full / NMX_R9_Head241.full | respective module | Canonical R8 afterValidate + R9 replay transitively |
| NMX_R9_Native241.full | 25–34 | Whole native observation → canonical relational replay → canonical Ref |
| NMX_R9_StageTwo.root | 25–41 | Native241.full on represented args; PortLaw241.canonical otherwise |

## Root0 handling already generic; reuse unchanged

NMS_R2Domains.entered lines 25–63 uses domain.2 (D2) on the SAME reads;
it takes arbitrary V and therefore obtains R0, not V0.Root0, at TAS.lib V0 R0 w.
NMS_R2Validate241.fold and NMX_R7_RelValidate241.fold similarly take arbitrary
V; NMX_R7_RelPublic241.fold/NMX_R7_RelReads241.fold and
NMX_R7_RelVerify241.call consume its exact Dom064. No canonical Root0 fact
is required there. NMS_R2Replay241.factor/modelVerify and NMS_R2Fold241.fold
are already library-parametric. NMS_R2Weak241 and NNP_Weak241.fold_env/fold_any
are specialisations, not the credited stage2 root.

The new proofs will reuse these generic lemmas unchanged. The two selection
associations above must be settled before promoting any parametric root for
NMX_R9_StageTwo.stage2. No spec, domain or credited implementation may change.
