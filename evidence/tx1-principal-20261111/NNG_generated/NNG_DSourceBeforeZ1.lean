import NNG_DSourceCircle1
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_DSourceBeforeZ1
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NMT_CallTree
open NNG_DProjection136 NNG_Observed136 NNG_DOccurrenceLaws136 NNG_SourceStep136 NNG_DLawStep136

/-- The reused getter value is a local fact derived at its first occurrence,
not a caller clause or a root hypothesis. No second native call/event is made. -/
theorem source (VL : RSL.VLib) (a : RSL.TX1_136.Args VL) {H W : Type}
    (p : Representation VL H) (c : Calls) (s : Parent H W)
    (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (env : RSL.Env)
    (alpha : Alpha) (claims : Claims) (extra : K29) (state : Array U8 32#usize)
    (z0 : aspis_core.circle.SecureCirclePoint) (t2 : r1_wire.SemanticTranscript H) (rec26 : r1_wire.ValidatedRecord)
    (saved : VL.validatedRecord a.prefix_ 26 = .ok (p.record rec26))
    (h : Laws VL a p c s events env (NNG_TreeSuffixes.f_r8 c s alpha claims extra state t2 z0 rec26 (.Ok rec26))) :
    NNG_Canonical136.beforeZ1 VL a (p.alpha alpha) (p.claims claims) (p.k29 extra) (p.b32 state)
      (p.point z0) (p.transcript t2) (p.record rec26) env
      (observation (output p) (events env)
        (NNG_TreeSuffixes.f_r8 c s alpha claims extra state t2 z0 rec26 (.Ok rec26))) := by
  let head := invoke "beforeZ1" (rec26,0#usize) (c.c15 29#usize rec26 0#usize)
  let k : core.result.Result K29 r1_wire.Error → Code (Output H) := fun r8 => do
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r8
    match cf with
    | core.ops.control_flow.ControlFlow.Continue before =>
      let cf9 ← core.result.Result.Insts.CoreOpsTry.branch (.Ok rec26 : core.result.Result r1_wire.ValidatedRecord r1_wire.Error)
      match cf9 with
      | core.ops.control_flow.ControlFlow.Continue vr3 =>
        NNG_TreeSuffixes.f_r9 c s alpha claims extra state t2 z0 before vr3
      | core.ops.control_flow.ControlFlow.Break residual =>
        monadLift <| core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      monadLift <| core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error) residual
  have split : NNG_TreeSuffixes.f_r8 c s alpha claims extra state t2 z0 rec26 (.Ok rec26) =
      NMT_CallTree.bind head k := rfl
  rw [split] at h ⊢
  have ent : NMT_CallTree.Event.call "beforeZ1" (rec26,0#usize) (c.c15 29#usize rec26 0#usize) ∈
      (run (NMT_CallTree.bind head k)).2 := entered _ _ _ _
  have headLaw : (RSL.RE.ofExcept (VL.decodeK29 (p.record rec26) 0)) env
      (observation (decodeReply p) (events env) head) := by
    rw [←h.beforeZ1 rec26 ent]
    exact call_actual (decodeReply p) events "beforeZ1" (rec26,0#usize) (c.c15 29#usize rec26 0#usize) env
  unfold NNG_Canonical136.beforeZ1 RSL.RE.bind
  refine bind_sound head k (decodeReply p) (output p) (events env) env _ _ headLaw ?_
  intro reply returned
  have next := after_return VL a p c s events env head k h reply returned
  cases reply with
  | Ok before =>
    have hn : Laws VL a p c s events env (NNG_TreeSuffixes.f_r9 c s alpha claims extra state t2 z0 before rec26) := by
      apply same_trace VL a p c s events env _ _ next
      rfl
    change NNG_Canonical136.record26b VL a (p.alpha alpha) (p.claims claims) (p.k29 extra) (p.k29 before)
      (p.b32 state) (p.point z0) (p.transcript t2) env
      (observation (output p) (events env) (NNG_TreeSuffixes.f_r9 c s alpha claims extra state t2 z0 before rec26))
    unfold NNG_Canonical136.record26b
    rw [saved]
    change RSL.RE.bind (RSL.RE.pure (p.record rec26)) _ env _
    rw [RSL.RE.bind_pure]
    exact NNG_DSourceCircle1.source VL a p c s events env alpha claims extra before state z0 t2 rec26 hn
  | Err e =>
    change (⟨.ret (.error (p.error e)),[]⟩ : RSL.Obs (Except VL.WErr (RSL.Verified VL))) = ⟨.ret (.error (p.error e)),[]⟩
    rfl
#print axioms source
end AspisR1.NNG_DSourceBeforeZ1
