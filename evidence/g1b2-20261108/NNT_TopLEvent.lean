import NNT_TopLCore
set_option autoImplicit false
namespace NNT_TopL
open RSL RSL.TAS RSL.NNT RSL.TFM RSL.EVB RSL.TASB
open RSL.TX2_241 (V2Lib Dom064)
open RSL.TX1_345 (S1Lib)
section
variable (S : Sig) (L : PoolLib) (D : DeployedIds) (V0 : V2Lib) (VL : VLib)
 (P : PreparedNew VL) (C : S1Lib VL) (I : Impl L V0 VL)
structure NNC_NMFPrimeB (g : NNC_G1aL S L V0 VL I) (R : RecSig S) where
  root0_or_rec : ∀ c, S.Exhibited c →
    (∀ a s env, TX2_213.Ref L D (lib V0 (fun _ _ => True) g.w) (TX1_344.asStage1 VL P C)
      a s env (I.entry a s env)) →
    (∃ s', (I.entry (S.args2 c) (S.state2 c) (S.env2 c)).exit = .ret (.ok (), s')) →
    S.Accepted1 c (S.model1 c) →
    S.Game c (S.model1 c) (S.model2 c) →
    S.Extraction c (S.model1 c) (S.model2 c) →
    S.Queries c (S.model1 c) →
    R.SelectsPair c →
    S.Root0Native c ∨ R.EventRec c

end
theorem event_top_splitB (S : Sig) (L : PoolLib) (D : DeployedIds) (V0 : V2Lib) (VL : VLib)
    (P : PreparedNew VL) (C : S1Lib VL) (I : Impl L V0 VL)
    (sp : Split S) (hl : Headline S) (a0 : A0_Digest S)
    (nmm : NMM_Roots L D V0 VL I) (nmx : NMX_Root L D V0 VL I) (nms : NMS_RootsL L D V0 VL I)
    (nmv : NMV_Roots L D V0 VL P C I) (nmw : NMW_Roots L D V0 VL P C I)
    (nmt : NMT_Roots L V0 VL P C I) (nmp : NMP_Roots L V0 VL P I) (nmo : NMO_Root L V0 VL I)
   
    (g1a : NNC_G1aL S L V0 VL I) (R : RecSig S) (rs : RecSelect S R)
    (nmfB : NNC_NMFPrimeB S L D V0 VL P C I g1a R) (r0 : NNC_R0Rep S V0)
    (a1 : NND_A1 S VL P C) (a2 : NND_A2 S L D V0)
    (a3 : NNE_A3 S VL P C) (a4 : NNE_A4 S L D V0) (a5 : NNE_A5 S L V0 VL P C I)
    (er : NNE_EntryRep S L V0 VL I)
    (c : S.Ctx) (hx : S.Exhibited c) (queries : S.Queries c (S.model1 c))
    (frame : S.GameFrame c) (trace : S.TraceRep c I.entry)
    (realizes : R.Realizes c)
    (ok1 : ∃ s', (I.entry (S.args1 c) (S.state1 c) (S.env1 c)).exit = .ret (.ok (), s'))
    (out1 : S.Out1 c (I.entry (S.args1 c) (S.state1 c) (S.env1 c)))
    (ok2 : ∃ s', (I.entry (S.args2 c) (S.state2 c) (S.env2 c)).exit = .ret (.ok (), s'))
    (out2 : S.Out2 c (I.entry (S.args2 c) (S.state2 c) (S.env2 c))) :
    S.Bound c (S.model1 c) (S.model2 c) ∧
      sp.Rest c (S.model1 c) (S.model2 c) ∧
      (sp.Outcome c (S.model1 c) (S.model2 c) ∨ R.EventRec c) := by
  have ext := a0.extraction c hx
  have bound := hl.numeric c _ _ ext queries
  have weak := weakEntry nmm nmx nms nmv nmw nmt nmp nmo g1a
  have stage1Ref : ∀ a s env, TX2_221.stage1Route a.data = true →
      TX1_344.Ref VL P C a s env (I.entry a s env) :=
    fun a s env h1 => ref213_stage1 h1 (weak a s env)
  have reject : ∀ a s env, TX2_221.admitted a.data = false →
      I.entry a s env = ⟨.ret (.error .invalidInstructionData, s), []⟩ :=
    fun a s env hn => ref213_reject hn (weak a s env)
  have recd := a5.recorded c a1 hx stage1Ref (asq8Frame nmm nmx nms nmv nmw nmt nmp nmo g1a)
    reject trace
  have game := S.mkGame c _ _ frame recd.1 recd.2
  have acc1 := a3.accepted1 c _ a1 hx (stage1Ref _ _ _ (er.route1 c frame trace)) ok1 out1
  have rest := sp.rest c _ _ ext acc1 game queries
  have sel := rs.selects c hx ext acc1 queries realizes
  refine ⟨bound, rest, ?_⟩
  rcases nmfB.root0_or_rec c hx weak ok2 acc1 game ext queries sel with root0 | ev
  · have ref240 := canonicalRef240 nmm nmx nms nmv nmw nmt nmp nmo
      (S.args2 c) (S.state2 c) (S.env2 c) (er.route2 c frame trace) (domain240_of_rep r0 c root0)
    have acc2 := a4.accepted2 c _ a2 hx ref240 ok2 out2
    exact Or.inl ((sp.concl_iff c _ _).mp (hl.deployed c _ _ ext acc1 acc2 game queries)).2
  · exact Or.inr ev


theorem event_top_splitB_full (S : Sig) (L : PoolLib) (D : DeployedIds) (V0 : V2Lib) (VL : VLib)
    (P : PreparedNew VL) (C : S1Lib VL) (I : Impl L V0 VL)
    (sp : Split S) (hl : Headline S) (a0 : A0_Digest S)
    (nmm : NMM_Roots L D V0 VL I) (nmx : NMX_Root L D V0 VL I) (nms : NMS_RootsL L D V0 VL I)
    (nmv : NMV_Roots L D V0 VL P C I) (nmw : NMW_Roots L D V0 VL P C I)
    (nmt : NMT_Roots L V0 VL P C I) (nmp : NMP_Roots L V0 VL P I) (nmo : NMO_Root L V0 VL I)
   
    (g1a : NNC_G1aL S L V0 VL I) (R : RecSig S) (rs : RecSelect S R) (hb : HeadlineB S R)
    (nmfB : NNC_NMFPrimeB S L D V0 VL P C I g1a R) (r0 : NNC_R0Rep S V0)
    (a1 : NND_A1 S VL P C) (a2 : NND_A2 S L D V0)
    (a3 : NNE_A3 S VL P C) (a4 : NNE_A4 S L D V0) (a5 : NNE_A5 S L V0 VL P C I)
    (er : NNE_EntryRep S L V0 VL I)
    (c : S.Ctx) (hx : S.Exhibited c) (queries : S.Queries c (S.model1 c))
    (frame : S.GameFrame c) (trace : S.TraceRep c I.entry)
    (realizes : R.Realizes c)
    (ok1 : ∃ s', (I.entry (S.args1 c) (S.state1 c) (S.env1 c)).exit = .ret (.ok (), s'))
    (out1 : S.Out1 c (I.entry (S.args1 c) (S.state1 c) (S.env1 c)))
    (ok2 : ∃ s', (I.entry (S.args2 c) (S.state2 c) (S.env2 c)).exit = .ret (.ok (), s'))
    (out2 : S.Out2 c (I.entry (S.args2 c) (S.state2 c) (S.env2 c))) :
    S.Bound c (S.model1 c) (S.model2 c) ∧
      sp.Rest c (S.model1 c) (S.model2 c) ∧
      (hb.OutcomeRec c (S.model1 c) (S.model2 c) ∨ R.EventRec c) := by
  have ext := a0.extraction c hx
  have bound := hl.numeric c _ _ ext queries
  have weak := weakEntry nmm nmx nms nmv nmw nmt nmp nmo g1a
  have stage1Ref : ∀ a s env, TX2_221.stage1Route a.data = true →
      TX1_344.Ref VL P C a s env (I.entry a s env) :=
    fun a s env h1 => ref213_stage1 h1 (weak a s env)
  have reject : ∀ a s env, TX2_221.admitted a.data = false →
      I.entry a s env = ⟨.ret (.error .invalidInstructionData, s), []⟩ :=
    fun a s env hn => ref213_reject hn (weak a s env)
  have recd := a5.recorded c a1 hx stage1Ref (asq8Frame nmm nmx nms nmv nmw nmt nmp nmo g1a)
    reject trace
  have game := S.mkGame c _ _ frame recd.1 recd.2
  have acc1 := a3.accepted1 c _ a1 hx (stage1Ref _ _ _ (er.route1 c frame trace)) ok1 out1
  have rest := sp.rest c _ _ ext acc1 game queries
  have sel := rs.selects c hx ext acc1 queries realizes
  refine ⟨bound, rest, ?_⟩
  rcases nmfB.root0_or_rec c hx weak ok2 acc1 game ext queries sel with root0 | ev
  · have ref240 := canonicalRef240 nmm nmx nms nmv nmw nmt nmp nmo
      (S.args2 c) (S.state2 c) (S.env2 c) (er.route2 c frame trace) (domain240_of_rep r0 c root0)
    have acc2 := a4.accepted2 c _ a2 hx ref240 ok2 out2
    exact Or.inl (hb.outcomeRec c _ _ ext acc1 acc2 game queries sel)
  · exact Or.inr ev



#print axioms event_top_splitB
#print axioms event_top_splitB_full
end NNT_TopL
