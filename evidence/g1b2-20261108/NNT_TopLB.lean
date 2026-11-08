import NNT_TopLEvent
set_option autoImplicit false
namespace NNT_TopL
open RSL RSL.TAS RSL.NNT RSL.TFM RSL.EVB RSL.TASB
open RSL.TX2_241 (V2Lib Dom064)
open RSL.TX1_345 (S1Lib)
variable {S : Sig} {R : RecSig S}
theorem top_splitB (L : PoolLib) (D : DeployedIds) (V0 : V2Lib) (VL : VLib)
    (P : PreparedNew VL) (C : S1Lib VL) (I : Impl L V0 VL)
    (sp : Split S) (hl : Headline S) (a0 : A0_Digest S)
    (nmm : NMM_Roots L D V0 VL I) (nmx : NMX_Root L D V0 VL I) (nms : NMS_RootsL L D V0 VL I)
    (nmv : NMV_Roots L D V0 VL P C I) (nmw : NMW_Roots L D V0 VL P C I)
    (nmt : NMT_Roots L V0 VL P C I) (nmp : NMP_Roots L V0 VL P I) (nmo : NMO_Root L V0 VL I)
   
    (g1a : NNC_G1aL S L V0 VL I) (rs : RecSelect S R) (hb : HeadlineB S R)
    (nmfB : NNC_NMFPrimeB S L D V0 VL P C I g1a R) (r0 : NNC_R0Rep S V0)
    (a1 : NND_A1 S VL P C) (a2 : NND_A2 S L D V0)
    (a3 : NNE_A3 S VL P C) (a4 : NNE_A4 S L D V0) (a5 : NNE_A5 S L V0 VL P C I)
    (er : NNE_EntryRep S L V0 VL I)
    (X : ExecB S R) (fx : X.Fixed) (w : X.World) (H : X.Oracle)
    (queries : X.QueriesF fx) (run : Runs S I (ctxB X fx w H)) :
    S.Bound (ctxB X fx w H) (S.model1 (ctxB X fx w H)) (S.model2 (ctxB X fx w H)) ∧
      sp.Rest (ctxB X fx w H) (S.model1 (ctxB X fx w H)) (S.model2 (ctxB X fx w H)) ∧
      (hb.OutcomeRec (ctxB X fx w H) (S.model1 (ctxB X fx w H)) (S.model2 (ctxB X fx w H)) ∨
        X.ERec fx H) := by
  have h := event_top_splitB_full S L D V0 VL P C I sp hl a0 nmm nmx nms nmv nmw nmt nmp nmo
    g1a R rs hb nmfB r0 a1 a2 a3 a4 a5 er (ctxB X fx w H)
    (X.exhibited_mk _ _ _ _ _) (X.queries_mk _ _ _ _ _ queries) run.frame run.trace
    (realizes_by_construction X fx w H) run.ok1 run.out1 run.ok2 run.out2
  rcases h with ⟨b, r, o | e⟩
  · exact ⟨b, r, Or.inl o⟩
  · exact ⟨b, r, Or.inr ((X.eventRec_mk _ _ _ _ _).mp e)⟩


theorem fail_sub_rec (L : PoolLib) (D : DeployedIds) (V0 : V2Lib) (VL : VLib)
    (P : PreparedNew VL) (C : S1Lib VL) (I : Impl L V0 VL)
    (sp : Split S) (hl : Headline S) (a0 : A0_Digest S)
    (nmm : NMM_Roots L D V0 VL I) (nmx : NMX_Root L D V0 VL I) (nms : NMS_RootsL L D V0 VL I)
    (nmv : NMV_Roots L D V0 VL P C I) (nmw : NMW_Roots L D V0 VL P C I)
    (nmt : NMT_Roots L V0 VL P C I) (nmp : NMP_Roots L V0 VL P I) (nmo : NMO_Root L V0 VL I)
   
    (g1a : NNC_G1aL S L V0 VL I) (rs : RecSelect S R) (hb : HeadlineB S R)
    (nmfB : NNC_NMFPrimeB S L D V0 VL P C I g1a R) (r0 : NNC_R0Rep S V0)
    (a1 : NND_A1 S VL P C) (a2 : NND_A2 S L D V0)
    (a3 : NNE_A3 S VL P C) (a4 : NNE_A4 S L D V0) (a5 : NNE_A5 S L V0 VL P C I)
    (er : NNE_EntryRep S L V0 VL I)
    (X : ExecB S R) (fx : X.Fixed) (w : X.World) (H : X.Oracle) (queries : X.QueriesF fx)
    (fail : Runs S I (ctxB X fx w H) ∧
      ¬ hb.OutcomeRec (ctxB X fx w H) (S.model1 (ctxB X fx w H)) (S.model2 (ctxB X fx w H))) :
    X.ERec fx H := by
  rcases (top_splitB L D V0 VL P C I sp hl a0 nmm nmx nms nmv nmw nmt nmp nmo g1a rs hb
    nmfB r0 a1 a2 a3 a4 a5 er X fx w H queries fail.1).2.2 with o | e
  · exact absurd o fail.2
  · exact e




theorem deployed_charge (L : PoolLib) (D : DeployedIds) (V0 : V2Lib) (VL : VLib)
    (P : PreparedNew VL) (C : S1Lib VL) (I : Impl L V0 VL)
    (sp : Split S) (hl : Headline S) (a0 : A0_Digest S)
    (nmm : NMM_Roots L D V0 VL I) (nmx : NMX_Root L D V0 VL I) (nms : NMS_RootsL L D V0 VL I)
    (nmv : NMV_Roots L D V0 VL P C I) (nmw : NMW_Roots L D V0 VL P C I)
    (nmt : NMT_Roots L V0 VL P C I) (nmp : NMP_Roots L V0 VL P I) (nmo : NMO_Root L V0 VL I)
   
    (g1a : NNC_G1aL S L V0 VL I) (rs : RecSelect S R) (hb : HeadlineB S R)
    (nmfB : NNC_NMFPrimeB S L D V0 VL P C I g1a R) (r0 : NNC_R0Rep S V0)
    (a1 : NND_A1 S VL P C) (a2 : NND_A2 S L D V0)
    (a3 : NNE_A3 S VL P C) (a4 : NNE_A4 S L D V0) (a5 : NNE_A5 S L V0 VL P C I)
    (er : NNE_EntryRep S L V0 VL I)
    (X : ExecB S R) (Ex : Expect X.Oracle) (fx : X.Fixed) (wOf : X.Oracle → X.World)
    (queries : X.QueriesF fx)
    (r m : X.Oracle → Rat) (T : Rat)
    (hm : ∀ H, 0 ≤ m H)
    (each : ∀ H, r H ≤ m H + ind (X.ERec fx H))
    (budget : Ex.E m + Ex.E (fun H => ind (X.ERec fx H)) ≤ T) :
    Ex.E (fun H => max (r H)
      (ind (Runs S I (ctxB X fx (wOf H) H) ∧
        ¬ hb.OutcomeRec (ctxB X fx (wOf H) H) (S.model1 (ctxB X fx (wOf H) H))
          (S.model2 (ctxB X fx (wOf H) H))))) ≤ T := by
  classical
  have pointwise : ∀ H, max (r H)
      (ind (Runs S I (ctxB X fx (wOf H) H) ∧
        ¬ hb.OutcomeRec (ctxB X fx (wOf H) H) (S.model1 (ctxB X fx (wOf H) H))
          (S.model2 (ctxB X fx (wOf H) H)))) ≤ m H + ind (X.ERec fx H) := by
    intro H
    rw [ind_def, ind_def]
    have e := each H
    rw [ind_def] at e
    exact no_second_charge (r H) (m H) (X.ERec fx H) _ (hm H) e
      (fun f => fail_sub_rec L D V0 VL P C I sp hl a0 nmm nmx nms nmv nmw nmt nmp nmo
        g1a rs hb nmfB r0 a1 a2 a3 a4 a5 er X fx (wOf H) H queries f)
  have h1 := Ex.mono _ _ pointwise
  rw [Ex.add] at h1
  exact Rat.le_trans h1 budget


#print axioms top_splitB
#print axioms fail_sub_rec
#print axioms deployed_charge
end NNT_TopL
