/-
TAS_TopB_NNE: split-B top in the form the merged NNE_ physical adapter needs.

Target not yet established.  Core Lean plus RSL_/TCK_/TAS_/TFM_/EVB_/TAS_TopB
and the merged NNE_SelectedRoutes (whose import closure is RSL-level: NNE_RslOk,
NMV_RslFold chain).  No sorry, no axiom declaration, no Root0 hypothesis.

The bare `TAS.NNE_EntryRep` field omits the actual Ok premises that the
selected routes depend on.  NNE_ (NNE_WIRING.md) therefore delivers the routes
from the weak entry reference plus the actual Ok observations and the account
counts (NNE_TopSplit.top_split, TFM form).  `top_splitB_counts` is that
theorem in full split-B form (both events E_rec, `realizes` premise), and
`top_splitB_physical` instantiates the pair from the adversary's execution
exactly as `TAS_TopB.top_splitB` does.  The counts are host facts
(`NNE_EntryArgs.count _ 3 _ _` and `_ 7 _ _`), not new premises.
-/
import TAS_TopB
import NNE_SelectedRoutes
set_option autoImplicit false

namespace RSL.TASB
open RSL.TAS RSL.TFM RSL.EVB
open TX2_241 (V2Lib Dom064)
open TX1_345 (S1Lib)

theorem top_splitB_counts (S : Sig) (L : PoolLib) (D : DeployedIds) (V0 : V2Lib) (VL : VLib)
    (P : PreparedNew VL) (C : S1Lib VL) (I : Impl L V0 VL)
    (sp : Split S) (hl : Headline S) (a0 : A0_Digest S)
    (nmm : NMM_Roots L D V0 VL I) (nmx : NMX_Root L D V0 VL I) (nms : NMS_Roots L D V0 VL I)
    (nmv : NMV_Roots L D V0 VL P C I) (nmw : NMW_Roots L D V0 VL P C I)
    (nmt : NMT_Roots L V0 VL P C I) (nmp : NMP_Roots L V0 VL P I) (nmo : NMO_Root L V0 VL I)
    (nmn : NMN_Root L V0 VL I)
    (g1a : NNC_G1a S L V0 VL I) (R : RecSig S) (rs : RecSelect S R) (hb : HeadlineB S R)
    (nmfB : NNC_NMFPrimeB S L D V0 VL P C I g1a R) (r0 : NNC_R0Rep S V0)
    (a1 : NND_A1 S VL P C) (a2 : NND_A2 S L D V0)
    (a3 : NNE_A3 S VL P C) (a4 : NNE_A4 S L D V0) (a5 : NNE_A5 S L V0 VL P C I)
    (c : S.Ctx) (hx : S.Exhibited c) (queries : S.Queries c (S.model1 c))
    (frame : S.GameFrame c) (trace : S.TraceRep c I.entry)
    (realizes : R.Realizes c)
    (ok1 : ∃ s', (I.entry (S.args1 c) (S.state1 c) (S.env1 c)).exit = .ret (.ok (), s'))
    (out1 : S.Out1 c (I.entry (S.args1 c) (S.state1 c) (S.env1 c)))
    (ok2 : ∃ s', (I.entry (S.args2 c) (S.state2 c) (S.env2 c)).exit = .ret (.ok (), s'))
    (count1 : (S.args1 c).accounts.length = 3)
    (count2 : (S.args2 c).accounts.length = 7)
    (out2 : S.Out2 c (I.entry (S.args2 c) (S.state2 c) (S.env2 c))) :
    S.Bound c (S.model1 c) (S.model2 c) ∧
      sp.Rest c (S.model1 c) (S.model2 c) ∧
      (hb.OutcomeRec c (S.model1 c) (S.model2 c) ∨ R.EventRec c) := by
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
  have rest := sp.rest c _ _ ext acc1 game queries
  have sel := rs.selects c hx ext acc1 queries realizes
  refine ⟨bound, rest, ?_⟩
  rcases nmfB.root0_or_rec c hx weak ok2 acc1 game ext queries sel with root0 | ev
  · have ref240 := canonicalRef240 nmm nmx nms nmv nmw nmt nmp nmo nmn
      (S.args2 c) (S.state2 c) (S.env2 c) route2 (domain240_of_rep r0 c root0)
    have acc2 := a4.accepted2 c _ a2 hx ref240 ok2 out2
    exact Or.inl (hb.outcomeRec c _ _ ext acc1 acc2 game queries sel)
  · exact Or.inr ev

/-- `top_splitB_counts` at the Realizes instantiation (pair := the adversary's
outputs at H; `realizes` by `⟨rfl, rfl⟩`). -/
theorem top_splitB_physical {S : Sig} {R : RecSig S}
    (L : PoolLib) (D : DeployedIds) (V0 : V2Lib) (VL : VLib)
    (P : PreparedNew VL) (C : S1Lib VL) (I : Impl L V0 VL)
    (sp : Split S) (hl : Headline S) (a0 : A0_Digest S)
    (nmm : NMM_Roots L D V0 VL I) (nmx : NMX_Root L D V0 VL I) (nms : NMS_Roots L D V0 VL I)
    (nmv : NMV_Roots L D V0 VL P C I) (nmw : NMW_Roots L D V0 VL P C I)
    (nmt : NMT_Roots L V0 VL P C I) (nmp : NMP_Roots L V0 VL P I) (nmo : NMO_Root L V0 VL I)
    (nmn : NMN_Root L V0 VL I)
    (g1a : NNC_G1a S L V0 VL I) (rs : RecSelect S R) (hb : HeadlineB S R)
    (nmfB : NNC_NMFPrimeB S L D V0 VL P C I g1a R) (r0 : NNC_R0Rep S V0)
    (a1 : NND_A1 S VL P C) (a2 : NND_A2 S L D V0)
    (a3 : NNE_A3 S VL P C) (a4 : NNE_A4 S L D V0) (a5 : NNE_A5 S L V0 VL P C I)
    (count1 : ∀ c, (S.args1 c).accounts.length = 3)
    (count2 : ∀ c, (S.args2 c).accounts.length = 7)
    (X : ExecB S R) (fx : X.Fixed) (w : X.World) (H : X.Oracle)
    (queries : X.QueriesF fx) (run : Runs S I (ctxB X fx w H)) :
    S.Bound (ctxB X fx w H) (S.model1 (ctxB X fx w H)) (S.model2 (ctxB X fx w H)) ∧
      sp.Rest (ctxB X fx w H) (S.model1 (ctxB X fx w H)) (S.model2 (ctxB X fx w H)) ∧
      (hb.OutcomeRec (ctxB X fx w H) (S.model1 (ctxB X fx w H)) (S.model2 (ctxB X fx w H)) ∨
        X.ERec fx H) := by
  have h := top_splitB_counts S L D V0 VL P C I sp hl a0 nmm nmx nms nmv nmw nmt nmp nmo nmn
    g1a R rs hb nmfB r0 a1 a2 a3 a4 a5 (ctxB X fx w H)
    (X.exhibited_mk _ _ _ _ _) (X.queries_mk _ _ _ _ _ queries) run.frame run.trace
    (realizes_by_construction X fx w H) run.ok1 run.out1 run.ok2 (count1 _) (count2 _) run.out2
  rcases h with ⟨b, r, o | e⟩
  · exact ⟨b, r, Or.inl o⟩
  · exact ⟨b, r, Or.inr ((X.eventRec_mk _ _ _ _ _).mp e)⟩

#print axioms top_splitB_counts
#print axioms top_splitB_physical

end RSL.TASB
