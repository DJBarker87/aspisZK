import NNG_DSourceRecord26
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_DSourceCircle0
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NMT_CallTree
open NNG_DProjection136 NNG_Observed136 NNG_DOccurrenceLaws136 NNG_SourceStep136 NNG_DLawStep136

theorem source (VL : RSL.VLib) (a : RSL.TX1_136.Args VL) {H W : Type}
    (p : Representation VL H) (c : Calls) (s : Parent H W)
    (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (env : RSL.Env)
    (alpha : Alpha) (claims : Claims) (extra : K29) (state : Array U8 32#usize)
    (t1 : r1_wire.SemanticTranscript H) (rec25 : r1_wire.ValidatedRecord)
    (h : Laws VL a p c s events env (NNG_TreeSuffixes.f_r6 c s alpha t1 claims extra state rec25)) :
    NNG_Canonical136.circle0 VL a (p.alpha alpha) (p.claims claims) (p.k29 extra)
      (p.b32 state) (p.transcript t1) (p.record rec25) env
      (observation (output p) (events env) (NNG_TreeSuffixes.f_r6 c s alpha t1 claims extra state rec25)) := by
  let head := invoke "circle0" (t1,rec25) (c.c13 s.digest t1 rec25)
  let k : (core.result.Result aspis_core.circle.SecureCirclePoint r1_wire.Error × r1_wire.SemanticTranscript H) → Code (Output H) :=
    fun (r6,t2) => do
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r6
      match cf with
      | core.ops.control_flow.ControlFlow.Continue z0 =>
        NNG_TreeSuffixes.f_r7 c s alpha claims extra state t2 z0
      | core.ops.control_flow.ControlFlow.Break residual =>
        monadLift <| core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error) residual
  have split : NNG_TreeSuffixes.f_r6 c s alpha t1 claims extra state rec25 = NMT_CallTree.bind head k := rfl
  rw [split] at h ⊢
  have ent : NMT_CallTree.Event.call "circle0" (t1,rec25) (c.c13 s.digest t1 rec25) ∈
      (run (NMT_CallTree.bind head k)).2 := entered _ _ _ _
  have headLaw : (VL.circle.run (p.transcript t1,p.record rec25)) env
      (observation (circleReply p) (events env) head) := by
    rw [←h.circle0 t1 rec25 ent]
    exact call_actual (circleReply p) events "circle0" (t1,rec25) (c.c13 s.digest t1 rec25) env
  unfold NNG_Canonical136.circle0 RSL.RE.bind
  refine bind_sound head k (circleReply p) (output p) (events env) env _ _ headLaw ?_
  intro reply returned
  have next := after_return VL a p c s events env head k h reply returned
  rcases reply with ⟨r6,t2⟩
  cases r6 with
  | Ok z0 =>
    have hn : Laws VL a p c s events env (NNG_TreeSuffixes.f_r7 c s alpha claims extra state t2 z0) := by
      apply same_trace VL a p c s events env _ _ next
      rfl
    change NNG_Canonical136.record26a VL a (p.alpha alpha) (p.claims claims) (p.k29 extra)
      (p.b32 state) (p.point z0) (p.transcript t2) env
      (observation (output p) (events env) (NNG_TreeSuffixes.f_r7 c s alpha claims extra state t2 z0))
    exact NNG_DSourceRecord26.source VL a p c s events env alpha claims extra state z0 t2 hn
  | Err e =>
    change (⟨.ret (.error (p.error e)),[]⟩ : RSL.Obs (Except VL.WErr (RSL.Verified VL))) = ⟨.ret (.error (p.error e)),[]⟩
    rfl
#print axioms source
end AspisR1.NNG_DSourceCircle0
