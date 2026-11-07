import NNG_DSourceMark5
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_DSourceCircle1
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NMT_CallTree
open NNG_DProjection136 NNG_Observed136 NNG_DOccurrenceLaws136 NNG_SourceStep136 NNG_DLawStep136

theorem source (VL : RSL.VLib) (a : RSL.TX1_136.Args VL) {H W : Type}
    (p : Representation VL H) (c : Calls) (s : Parent H W)
    (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (env : RSL.Env)
    (alpha : Alpha) (claims : Claims) (extra before : K29) (state : Array U8 32#usize)
    (z0 : aspis_core.circle.SecureCirclePoint) (t2 : r1_wire.SemanticTranscript H) (rec26 : r1_wire.ValidatedRecord)
    (h : Laws VL a p c s events env (NNG_TreeSuffixes.f_r9 c s alpha claims extra state t2 z0 before rec26)) :
    NNG_Canonical136.circle1 VL a (p.alpha alpha) (p.claims claims) (p.k29 extra) (p.k29 before)
      (p.b32 state) (p.point z0) (p.transcript t2) (p.record rec26) env
      (observation (output p) (events env)
        (NNG_TreeSuffixes.f_r9 c s alpha claims extra state t2 z0 before rec26)) := by
  let head := invoke "circle1" (t2,rec26) (c.c13 s.digest t2 rec26)
  let k : (core.result.Result aspis_core.circle.SecureCirclePoint r1_wire.Error × r1_wire.SemanticTranscript H) → Code (Output H) :=
    fun (r9,t3) => do
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r9
      match cf with
      | core.ops.control_flow.ControlFlow.Continue z1 =>
        NNG_TreeSuffixes.f_mark5 c s alpha claims extra state z0 before t3 z1
      | core.ops.control_flow.ControlFlow.Break residual =>
        monadLift <| core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error) residual
  have split : NNG_TreeSuffixes.f_r9 c s alpha claims extra state t2 z0 before rec26 =
      NMT_CallTree.bind head k := rfl
  rw [split] at h ⊢
  have ent : NMT_CallTree.Event.call "circle1" (t2,rec26) (c.c13 s.digest t2 rec26) ∈
      (run (NMT_CallTree.bind head k)).2 := entered _ _ _ _
  have headLaw : (VL.circle.run (p.transcript t2,p.record rec26)) env
      (observation (circleReply p) (events env) head) := by
    rw [←h.circle1 t2 rec26 ent]
    exact call_actual (circleReply p) events "circle1" (t2,rec26) (c.c13 s.digest t2 rec26) env
  unfold NNG_Canonical136.circle1 RSL.RE.bind
  refine bind_sound head k (circleReply p) (output p) (events env) env _ _ headLaw ?_
  intro reply returned
  have next := after_return VL a p c s events env head k h reply returned
  rcases reply with ⟨r9,t3⟩
  cases r9 with
  | Ok z1 =>
    have hn : Laws VL a p c s events env (NNG_TreeSuffixes.f_mark5 c s alpha claims extra state z0 before t3 z1) := by
      apply same_trace VL a p c s events env _ _ next
      rfl
    change NNG_Canonical136.circleGuard VL a (p.alpha alpha) (p.claims claims) (p.k29 extra) (p.k29 before)
      (p.b32 state) (p.point z0) (p.point z1) (p.transcript t3) env
      (observation (output p) (events env)
        (NNG_TreeSuffixes.f_mark5 c s alpha claims extra state z0 before t3 z1))
    exact NNG_DSourceMark5.source VL a p c s events env alpha claims extra before state z0 z1 t3 hn
  | Err e =>
    change (⟨.ret (.error (p.error e)),[]⟩ : RSL.Obs (Except VL.WErr (RSL.Verified VL))) =
      ⟨.ret (.error (p.error e)),[]⟩
    rfl
#print axioms source
end AspisR1.NNG_DSourceCircle1
