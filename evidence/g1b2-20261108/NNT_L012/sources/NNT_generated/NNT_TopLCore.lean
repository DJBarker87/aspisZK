import NNT_G1aLaw
import TAS_TopB_NNE
set_option autoImplicit false
namespace NNT_TopL
open RSL RSL.TAS RSL.NNT RSL.TFM RSL.EVB RSL.TASB
open RSL.TX2_241 (V2Lib Dom064)
open RSL.TX1_345 (S1Lib)
section
variable (S : Sig) (L : PoolLib) (D : DeployedIds) (V0 : V2Lib) (VL : VLib)
 (P : PreparedNew VL) (C : S1Lib VL) (I : Impl L V0 VL)
structure NNC_NMFPrime (g : NNC_G1aL S L V0 VL I) where
  Ev : S.Ctx → Prop
  root0_or_event : ∀ c, S.Exhibited c →
    (∀ a s env, TX2_213.Ref L D (lib V0 (fun _ _ => True) g.w) (TX1_344.asStage1 VL P C)
      a s env (I.entry a s env)) →
    (∃ s', (I.entry (S.args2 c) (S.state2 c) (S.env2 c)).exit = .ret (.ok (), s')) →
    S.Accepted1 c (S.model1 c) →
    S.Game c (S.model1 c) (S.model2 c) →
    S.Extraction c (S.model1 c) (S.model2 c) →
    S.Queries c (S.model1 c) →
    S.Root0Native c ∨ Ev c


structure NNC_CaseSplit {g : NNC_G1aL S L V0 VL I} (nmf : NNC_NMFPrime S L D V0 VL P C I g) where
  event_eq : ∀ c, nmf.Ev c → S.Event c (S.model1 c)



end
section Compose
variable {L : PoolLib} {D : DeployedIds} {V0 : V2Lib} {VL : VLib}
  {P : PreparedNew VL} {C : S1Lib VL} {I : Impl L V0 VL}


theorem stage1Root (nmo : NMO_Root L V0 VL I) (nmp : NMP_Roots L V0 VL P I)
    (nmt : NMT_Roots L V0 VL P C I) (nmv : NMV_Roots L D V0 VL P C I) :
    TX1_344.RowSpec_344 VL P C I.f344 :=
  nmv.r344 (nmt.r345 (nmt.r328 (nmt.r094 (nmp.r087 (nmp.r137 nmo.r136)))))


theorem validateRoot (nmm : NMM_Roots L D V0 VL I) (nmx : NMX_Root L D V0 VL I)
    (nms : NMS_RootsL L D V0 VL I) : TX2_242.RowSpec_242 L D I.f242 :=
  nms.r242 (nmx.r233 nmm.r234 nmm.r217)


theorem entryRoot (nmm : NMM_Roots L D V0 VL I) (nmx : NMX_Root L D V0 VL I)
    (nms : NMS_RootsL L D V0 VL I) (nmv : NMV_Roots L D V0 VL P C I)
    (nmw : NMW_Roots L D V0 VL P C I) (nmt : NMT_Roots L V0 VL P C I)
    (nmp : NMP_Roots L V0 VL P I) (nmo : NMO_Root L V0 VL I)
    (R0 : Bytes → Bytes → Prop) (w : Bytes → Bytes → Bytes → Spec (Except V0.VErr Unit))
    (h : LawRefines V0 R0 w) :
    TX1_330.RowSpec_330 L D (lib V0 R0 w) VL P C I.entry :=
  nmw.r213 _ (nmw.r221 _ (stage1Root nmo nmp nmt nmv)
    (nmv.r240 _ (nms.r241 R0 w h (validateRoot nmm nmx nms))))


theorem row333_is_221 (V : V2Lib) :
    TX1_333.RowSpec_333 L D V VL P C I.process =
      TX2_221.RowSpec_221 L D V (TX1_344.asStage1 VL P C) I.process := rfl

theorem row330_is_213 (V : V2Lib) :
    TX1_330.RowSpec_330 L D V VL P C I.entry =
      TX2_213.RowSpec_213 L D V (TX1_344.asStage1 VL P C) I.entry := rfl


theorem weakEntry (nmm : NMM_Roots L D V0 VL I) (nmx : NMX_Root L D V0 VL I)
    (nms : NMS_RootsL L D V0 VL I) (nmv : NMV_Roots L D V0 VL P C I)
    (nmw : NMW_Roots L D V0 VL P C I) (nmt : NMT_Roots L V0 VL P C I)
    (nmp : NMP_Roots L V0 VL P I) (nmo : NMO_Root L V0 VL I)
    {S : Sig} (g : NNC_G1aL S L V0 VL I) :
    ∀ a s env, TX2_213.Ref L D (lib V0 (fun _ _ => True) g.w) (TX1_344.asStage1 VL P C)
      a s env (I.entry a s env) :=
  TCK.entry_weak_unconditional L D V0 g.w VL P C I.entry
    (entryRoot nmm nmx nms nmv nmw nmt nmp nmo _ _ g.lawRefines)


theorem canonicalRef240 (nmm : NMM_Roots L D V0 VL I) (nmx : NMX_Root L D V0 VL I)
    (nms : NMS_RootsL L D V0 VL I) (nmv : NMV_Roots L D V0 VL P C I)
    (nmw : NMW_Roots L D V0 VL P C I) (nmt : NMT_Roots L V0 VL P C I)
    (nmp : NMP_Roots L V0 VL P I) (nmo : NMO_Root L V0 VL I)
    (a : TX2_213.Args) (s : SdkState) (env : Env) (hq : ASQ8 a.data)
    (dom : TX2_240.Domain V0 a s) :
    TX2_240.Ref L D V0 a s env (I.entry a s env) :=
  ref213_asq8 hq
    (entryRoot nmm nmx nms nmv nmw nmt nmp nmo V0.Root0 V0.tx2auth (lawRefines_canonical V0) a s env
      ⟨fun _ _ => dom, fun _ _ => trivial⟩)


theorem asq8Frame (nmm : NMM_Roots L D V0 VL I) (nmx : NMX_Root L D V0 VL I)
    (nms : NMS_RootsL L D V0 VL I) (nmv : NMV_Roots L D V0 VL P C I)
    (nmw : NMW_Roots L D V0 VL P C I) (nmt : NMT_Roots L V0 VL P C I)
    (nmp : NMP_Roots L V0 VL P I) (nmo : NMO_Root L V0 VL I)
    {S : Sig} (g : NNC_G1aL S L V0 VL I) :
    ∀ a s env, ASQ8 a.data → Frame s (I.entry a s env) :=
  fun a s env hq => nmv.g2 g.w g.writeFree a s env _
    (ref213_asq8 hq (weakEntry nmm nmx nms nmv nmw nmt nmp nmo g a s env))


theorem domain240_of_rep {S : Sig} (r0 : NNC_R0Rep S V0) (c : S.Ctx) (h : S.Root0Native c) :
    TX2_240.Domain V0 (S.args2 c) (S.state2 c) :=
  fun a0 a6 h7 h0 h6 l6 l0 => r0.rep c a0 a6 h h7 h0 h6 l6 l0

end Compose


theorem top (S : Sig) (L : PoolLib) (D : DeployedIds) (V0 : V2Lib) (VL : VLib)
    (P : PreparedNew VL) (C : S1Lib VL) (I : Impl L V0 VL)
    -- existing headline (no job)
    (hl : Headline S)
    -- A0 (G0 job)
    (a0 : A0_Digest S)
    -- row roots, RSL form
    (nmm : NMM_Roots L D V0 VL I) (nmx : NMX_Root L D V0 VL I) (nms : NMS_RootsL L D V0 VL I)
    (nmv : NMV_Roots L D V0 VL P C I) (nmw : NMW_Roots L D V0 VL P C I)
    (nmt : NMT_Roots L V0 VL P C I) (nmp : NMP_Roots L V0 VL P I) (nmo : NMO_Root L V0 VL I)
   
    -- NNC_
    (g1a : NNC_G1aL S L V0 VL I) (nmf : NNC_NMFPrime S L D V0 VL P C I g1a)
    (cs : NNC_CaseSplit S L D V0 VL P C I nmf) (r0 : NNC_R0Rep S V0)
    -- NND_
    (a1 : NND_A1 S VL P C) (a2 : NND_A2 S L D V0)
    -- NNE_
    (a3 : NNE_A3 S VL P C) (a4 : NNE_A4 S L D V0) (a5 : NNE_A5 S L V0 VL P C I)
    (er : NNE_EntryRep S L V0 VL I)
    -- the deployed pair: headline binders retained, plus the actual run
    (c : S.Ctx) (hx : S.Exhibited c) (queries : S.Queries c (S.model1 c))
    (frame : S.GameFrame c) (trace : S.TraceRep c I.entry)
    (ok1 : ∃ s', (I.entry (S.args1 c) (S.state1 c) (S.env1 c)).exit = .ret (.ok (), s'))
    (out1 : S.Out1 c (I.entry (S.args1 c) (S.state1 c) (S.env1 c)))
    (ok2 : ∃ s', (I.entry (S.args2 c) (S.state2 c) (S.env2 c)).exit = .ret (.ok (), s'))
    (out2 : S.Out2 c (I.entry (S.args2 c) (S.state2 c) (S.env2 c))) :
    S.Bound c (S.model1 c) (S.model2 c) ∧
      (S.Concl c (S.model1 c) (S.model2 c) ∨ S.Event c (S.model1 c)) := by
  -- extraction at native := model (A0); Root0-free bound
  have ext := a0.extraction c hx
  have bound := hl.numeric c _ _ ext queries
  -- weak (Root0-free) entry facts
  have weak := weakEntry nmm nmx nms nmv nmw nmt nmp nmo g1a
  have stage1Ref : ∀ a s env, TX2_221.stage1Route a.data = true →
      TX1_344.Ref VL P C a s env (I.entry a s env) :=
    fun a s env h1 => ref213_stage1 h1 (weak a s env)
  have reject : ∀ a s env, TX2_221.admitted a.data = false →
      I.entry a s env = ⟨.ret (.error .invalidInstructionData, s), []⟩ :=
    fun a s env hn => ref213_reject hn (weak a s env)
  -- game (A5 with G2), accepted1 (A3): no Root0
  have recd := a5.recorded c a1 hx stage1Ref (asq8Frame nmm nmx nms nmv nmw nmt nmp nmo g1a)
    reject trace
  have game := S.mkGame c _ _ frame recd.1 recd.2
  have acc1 := a3.accepted1 c _ a1 hx (stage1Ref _ _ _ (er.route1 c frame trace)) ok1 out1
  -- case split (NMF′)
  refine ⟨bound, ?_⟩
  rcases nmf.root0_or_event c hx weak ok2 acc1 game ext queries with root0 | ev
  · -- Root0 branch: canonical chain, accepted2 (A4), existing headline
    have ref240 := canonicalRef240 nmm nmx nms nmv nmw nmt nmp nmo
      (S.args2 c) (S.state2 c) (S.env2 c) (er.route2 c frame trace) (domain240_of_rep r0 c root0)
    have acc2 := a4.accepted2 c _ a2 hx ref240 ok2 out2
    exact Or.inl (hl.deployed c _ _ ext acc1 acc2 game queries)
  · -- event branch: the headline's own charged event
    exact Or.inr (cs.event_eq c ev)


#print axioms stage1Root
#print axioms validateRoot
#print axioms entryRoot
#print axioms row333_is_221
#print axioms row330_is_213
#print axioms weakEntry
#print axioms canonicalRef240
#print axioms asq8Frame
#print axioms domain240_of_rep
#print axioms top
end NNT_TopL
