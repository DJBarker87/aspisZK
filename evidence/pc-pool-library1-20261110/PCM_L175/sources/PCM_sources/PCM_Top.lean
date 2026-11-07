import EVB_EventB
import PCM_Inst_Registry
import PCM_Inst_Deployed
import PCM_Spec_POOL_328
import PCM_Spec_POOL_330
import PCM_Spec_POOL_327
set_option autoImplicit false
namespace PCM_Top
open RSL RSL.TAS RSL.TFM RSL.EVB
open RSL.TX2_241 (V2Lib Dom064)
open RSL.TX1_345 (S1Lib)
/-- All three owner specifications remain full Result/effect/prefix laws. -/
structure Owners where
  depositChildren : PCM_POOL_328.Children
  terminalChildren : PCM_POOL_330.Children
  checkpointChildren : PCM_POOL_327.Children
  runtime : PCM.Runtime
  deposit : PCM_POOL_328.Args → PCM.State → RSL.Env → PCM.Observation Unit
  terminal : PCM_POOL_330.Args → UInt64 → PCM.State → RSL.Env → PCM.Observation Unit
  checkpoint : PCM_POOL_327.Args → PCM.State → RSL.Env → PCM.Observation Unit

def Owners.Spec (o : Owners) : Prop :=
  PCM_POOL_328.RowSpec o.depositChildren o.runtime o.deposit ∧
  PCM_POOL_330.RowSpec o.terminalChildren o.runtime o.terminal ∧
  PCM_POOL_327.RowSpec o.checkpointChildren o.checkpoint

/-- Typed outstanding physical/entry/top bridges. These are named obligations,
not a proved installation. Pool:330 is NOT verifier TX1:330. No field asserts
Root0 unconditionally. Same-occurrence Root0 OR existing E_rec belongs to nmfB. -/
structure Payload (S : Sig) (L : PoolLib) (D : DeployedIds) (V0 : V2Lib) (VL : VLib) (P : PreparedNew VL) (C : S1Lib VL) (I : Impl L V0 VL) (R : RecSig S) where
  sp : Split S
  hl : Headline S
  a0 : A0_Digest S
  nmm : NMM_Roots L D V0 VL I
  nmx : NMX_Root L D V0 VL I
  nms : NMS_Roots L D V0 VL I
  nmv : NMV_Roots L D V0 VL P C I
  nmw : NMW_Roots L D V0 VL P C I
  nmt : NMT_Roots L V0 VL P C I
  nmp : NMP_Roots L V0 VL P I
  nmo : NMO_Root L V0 VL I
  nmn : NMN_Root L V0 VL I
  g1a : NNC_G1a S L V0 VL I
  rs : RecSelect S R
  hb : HeadlineB S R
  nmfB : NNC_NMFPrimeB S L D V0 VL P C I g1a R
  r0 : NNC_R0Rep S V0
  a1 : NND_A1 S VL P C
  a2 : NND_A2 S L D V0
  a3 : NNE_A3 S VL P C
  a4 : NNE_A4 S L D V0
  a5 : NNE_A5 S L V0 VL P C I
  er : NNE_EntryRep S L V0 VL I

/-- Supporting skeleton only: `assemble` is the still-open association of the
Pool owners with the verifier entry, physical CPI and headline interfaces.
Realizes/RZ-STATE is NOT discharged by this theorem or used to filter worlds. -/
theorem check (S : Sig) (L : PoolLib) (D : DeployedIds) (V0 : V2Lib) (VL : VLib) (P : PreparedNew VL) (C : S1Lib VL) (I : Impl L V0 VL) (R : RecSig S)
    (owners : Owners) (ownerSpecs : owners.Spec)
    (assemble : owners.Spec → Payload S L D V0 VL P C I R)
    (c : S.Ctx)
    (hx : S.Exhibited c)
    (queries : S.Queries c (S.model1 c))
    (frame : S.GameFrame c)
    (trace : S.TraceRep c I.entry)
    (realizes : R.Realizes c)
    (ok1 : ∃ s', (I.entry (S.args1 c) (S.state1 c) (S.env1 c)).exit = .ret (.ok (), s'))
    (out1 : S.Out1 c (I.entry (S.args1 c) (S.state1 c) (S.env1 c)))
    (ok2 : ∃ s', (I.entry (S.args2 c) (S.state2 c) (S.env2 c)).exit = .ret (.ok (), s'))
    (out2 : S.Out2 c (I.entry (S.args2 c) (S.state2 c) (S.env2 c)))
    : S.Bound c (S.model1 c) (S.model2 c) ∧
      (assemble ownerSpecs).sp.Rest c (S.model1 c) (S.model2 c) ∧
      ((assemble ownerSpecs).hb.OutcomeRec c (S.model1 c) (S.model2 c) ∨ R.EventRec c) := by
  let p := assemble ownerSpecs
  exact RSL.EVB.top_splitB_full S L D V0 VL P C I p.sp p.hl p.a0 p.nmm p.nmx p.nms p.nmv p.nmw p.nmt p.nmp p.nmo p.nmn p.g1a R p.rs p.hb p.nmfB p.r0 p.a1 p.a2 p.a3 p.a4 p.a5 p.er c hx queries frame trace realizes ok1 out1 ok2 out2 

/-- Shared interface is literal; there is no second PoolLib. -/
theorem shared_type : PCM.SharedPoolLib = RSL.PoolLib := rfl
#print axioms check
#print axioms shared_type
end PCM_Top
