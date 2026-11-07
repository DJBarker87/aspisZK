import NNE_SelectedRoutes
import NNE_RecordSig
import TFM_TopExact
set_option autoImplicit false
namespace NNE_TopSplit
open RSL RSL.TAS RSL.TFM
open RSL.TX2_241 (V2Lib)
open RSL.TX1_345 (S1Lib)
/- Same split form as TFM, deriving selected routes from the already required
actual Ok observations and the concrete account counts. TAS.EntryRep's field
omits Ok; this theorem needs no stronger physical-trace premise to repair it.
No adopted-headline or security-number claim is made. -/
theorem top_split (S : Sig) (L : PoolLib) (D : DeployedIds) (V0 : V2Lib) (VL : VLib)
    (P : PreparedNew VL) (C : S1Lib VL) (I : Impl L V0 VL)
    (sp : Split S) (hl : Headline S) (a0 : A0_Digest S)
    (nmm : NMM_Roots L D V0 VL I) (nmx : NMX_Root L D V0 VL I) (nms : NMS_Roots L D V0 VL I)
    (nmv : NMV_Roots L D V0 VL P C I) (nmw : NMW_Roots L D V0 VL P C I)
    (nmt : NMT_Roots L V0 VL P C I) (nmp : NMP_Roots L V0 VL P I) (nmo : NMO_Root L V0 VL I)
    (nmn : NMN_Root L V0 VL I)
    (g1a : NNC_G1a S L V0 VL I) (nmf : NNC_NMFPrime S L D V0 VL P C I g1a)
    (cs : NNC_CaseSplit S L D V0 VL P C I nmf) (r0 : NNC_R0Rep S V0)
    (a1 : NND_A1 S VL P C) (a2 : NND_A2 S L D V0)
    (a3 : NNE_A3 S VL P C) (a4 : NNE_A4 S L D V0) (a5 : NNE_A5 S L V0 VL P C I)
    (c : S.Ctx) (hx : S.Exhibited c) (queries : S.Queries c (S.model1 c))
    (frame : S.GameFrame c) (trace : S.TraceRep c I.entry)
    (ok1 : ∃ s', (I.entry (S.args1 c) (S.state1 c) (S.env1 c)).exit = .ret (.ok (), s'))
    (out1 : S.Out1 c (I.entry (S.args1 c) (S.state1 c) (S.env1 c)))
    (ok2 : ∃ s', (I.entry (S.args2 c) (S.state2 c) (S.env2 c)).exit = .ret (.ok (), s'))
    (count1 : (S.args1 c).accounts.length = 3)
    (count2 : (S.args2 c).accounts.length = 7)
    (out2 : S.Out2 c (I.entry (S.args2 c) (S.state2 c) (S.env2 c))) :
    S.Bound c (S.model1 c) (S.model2 c) ∧
      sp.Rest c (S.model1 c) (S.model2 c) ∧
      (sp.Outcome c (S.model1 c) (S.model2 c) ∨ S.Event c (S.model1 c)) := by
  have ext := a0.extraction c hx
  have bound := hl.numeric c _ _ ext queries
  have weak := weakEntry nmm nmx nms nmv nmw nmt nmp nmo g1a
  have route1 := NNE_SelectedRoutes.first L D _ VL P C (S.args1 c) (S.state1 c)
    (S.env1 c) _ count1 (weak _ _ _) ok1
  have route2 := NNE_SelectedRoutes.second L D _ VL P C (S.args2 c) (S.state2 c)
    (S.env2 c) _ count2 (weak _ _ _) ok2
  have stage1Ref : ∀ a s env, TX2_221.stage1Route a.data = true →
      TX1_344.Ref VL P C a s env (I.entry a s env) :=
    fun a s env h1 => ref213_stage1 h1 (weak a s env)
  have reject : ∀ a s env, TX2_221.admitted a.data = false →
      I.entry a s env = ⟨.ret (.error .invalidInstructionData, s), []⟩ :=
    fun a s env hn => ref213_reject hn (weak a s env)
  have recd := a5.recorded c a1 hx stage1Ref (asq8Frame nmm nmx nms nmv nmw nmt nmp nmo g1a)
    reject trace
  have game := S.mkGame c _ _ frame recd.1 recd.2
  have acc1 := a3.accepted1 c _ a1 hx (stage1Ref _ _ _ route1) ok1 out1
  -- the ten non-Outcome conjuncts: Root0-free
  have rest := sp.rest c _ _ ext acc1 game queries
  refine ⟨bound, rest, ?_⟩
  rcases nmf.root0_or_event c hx weak ok2 acc1 game ext queries with root0 | ev
  · have ref240 := canonicalRef240 nmm nmx nms nmv nmw nmt nmp nmo nmn
      (S.args2 c) (S.state2 c) (S.env2 c) route2 (domain240_of_rep r0 c root0)
    have acc2 := a4.accepted2 c _ a2 hx ref240 ok2 out2
    exact Or.inl ((sp.concl_iff c _ _).mp (hl.deployed c _ _ ext acc1 acc2 game queries)).2
  · exact Or.inr (cs.event_eq c ev)


#print axioms top_split
end NNE_TopSplit
