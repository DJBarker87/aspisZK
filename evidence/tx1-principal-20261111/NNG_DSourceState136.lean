import NNG_DSourceCircle0
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_DSourceState136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NMT_CallTree
open NNG_DProjection136 NNG_Observed136 NNG_DOccurrenceLaws136 NNG_SourceStep136 NNG_DLawStep136

theorem source (VL : RSL.VLib) (a : RSL.TX1_136.Args VL) {H W : Type}
    (p : Representation VL H) (c : Calls) (s : Parent H W)
    (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (env : RSL.Env)
    (alpha : Alpha) (claims : Claims) (extra : K29) (t1 : r1_wire.SemanticTranscript H) (rec25 : r1_wire.ValidatedRecord)
    (saved : VL.validatedRecord a.prefix_ 25 = .ok (p.record rec25))
    (h : Laws VL a p c s events env (NNG_TreeSuffixes.f_state_before_z0 c s alpha t1 claims extra (.Ok rec25))) :
    NNG_Canonical136.stateBefore VL a (p.alpha alpha) (p.claims claims) (p.k29 extra) (p.transcript t1) env
      (observation (output p) (events env) (NNG_TreeSuffixes.f_state_before_z0 c s alpha t1 claims extra (.Ok rec25))) := by
  let head := invoke "state" t1 (c.c14 s.digest t1)
  let k : Array U8 32#usize → Code (Output H) := fun state => do
    let cf ← core.result.Result.Insts.CoreOpsTry.branch (.Ok rec25 : core.result.Result r1_wire.ValidatedRecord r1_wire.Error)
    match cf with
    | core.ops.control_flow.ControlFlow.Continue vr1 => NNG_TreeSuffixes.f_r6 c s alpha t1 claims extra state vr1
    | core.ops.control_flow.ControlFlow.Break residual =>
      monadLift <| core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error) residual
  have split : NNG_TreeSuffixes.f_state_before_z0 c s alpha t1 claims extra (.Ok rec25) = NMT_CallTree.bind head k := rfl
  rw [split] at h ⊢
  have ent : NMT_CallTree.Event.call "state" t1 (c.c14 s.digest t1) ∈ (run (NMT_CallTree.bind head k)).2 := entered _ _ _ _
  have headLaw : RSL.Spec.pure (VL.state (p.transcript t1)) env (observation p.b32 (events env) head) := by
    rw [←h.state t1 ent]
    exact call_actual p.b32 events "state" t1 (c.c14 s.digest t1) env
  unfold NNG_Canonical136.stateBefore
  rw [RSL.RE.bind_pure]
  refine pure_bind_sound head k p.b32 (output p) (events env) env (VL.state (p.transcript t1))
    (fun state => NNG_Canonical136.record25b VL a (p.alpha alpha) (p.claims claims) (p.k29 extra) state (p.transcript t1)) headLaw ?_
  intro state returned
  have next := after_return VL a p c s events env head k h state returned
  have hn : Laws VL a p c s events env (NNG_TreeSuffixes.f_r6 c s alpha t1 claims extra state rec25) := by
    apply same_trace VL a p c s events env _ _ next
    rfl
  change NNG_Canonical136.record25b VL a (p.alpha alpha) (p.claims claims) (p.k29 extra) (p.b32 state) (p.transcript t1) env
    (observation (output p) (events env) (NNG_TreeSuffixes.f_r6 c s alpha t1 claims extra state rec25))
  unfold NNG_Canonical136.record25b
  rw [saved]
  change RSL.RE.bind (RSL.RE.pure (p.record rec25)) _ env _
  rw [RSL.RE.bind_pure]
  exact NNG_DSourceCircle0.source VL a p c s events env alpha claims extra state t1 rec25 hn
#print axioms source
end AspisR1.NNG_DSourceState136
