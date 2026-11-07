import NNG_DSourceTerminal
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_DSourceClaims
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NMT_CallTree
open NNG_DProjection136 NNG_Observed136 NNG_DOccurrenceLaws136 NNG_SourceStep136 NNG_DLawStep136

theorem source (VL : RSL.VLib) (a : RSL.TX1_136.Args VL) {H W : Type}
    (p : Representation VL H) (c : Calls) (s : Parent H W)
    (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (env : RSL.Env)
    (running : Q) (alpha : Alpha) (t1 : r1_wire.SemanticTranscript H) (runningDom : p.qDom running)
    (h : Laws VL a p c s events env (NNG_TreeSuffixes.f_r1 c s running alpha t1)) :
    NNG_Canonical136.claims VL a (p.q running) (p.alpha alpha) (p.transcript t1) env
      (observation (output p) (events env) (NNG_TreeSuffixes.f_r1 c s running alpha t1)) := by
  let head := invoke "claims" s.prefixValue (c.c8 s.prefixValue)
  let k : core.result.Result Claims r1_wire.Error → Code (Output H) := fun r1 => do
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf with
    | core.ops.control_flow.ControlFlow.Continue claims =>
      NNG_TreeSuffixes.f_r2 c s running alpha t1 claims
    | core.ops.control_flow.ControlFlow.Break residual =>
      monadLift <| core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error) residual
  have split : NNG_TreeSuffixes.f_r1 c s running alpha t1 = NMT_CallTree.bind head k := rfl
  rw [split] at h ⊢
  have ent : NMT_CallTree.Event.call "claims" s.prefixValue (c.c8 s.prefixValue) ∈
      (run (NMT_CallTree.bind head k)).2 := entered _ _ _ _
  have headLaw : (VL.claims.run a.prefix_) env (observation (claimsReply p) (events env) head) := by
    rw [←h.claims ent]
    exact call_actual (claimsReply p) events "claims" s.prefixValue (c.c8 s.prefixValue) env
  unfold NNG_Canonical136.claims RSL.RE.bind
  refine bind_sound head k (claimsReply p) (output p) (events env) env _ _ headLaw ?_
  intro reply returned
  have next := after_return VL a p c s events env head k h reply returned
  cases reply with
  | Ok claims =>
    have hn : Laws VL a p c s events env (NNG_TreeSuffixes.f_r2 c s running alpha t1 claims) := by
      apply same_trace VL a p c s events env _ _ next
      rfl
    change NNG_Canonical136.terminal VL a (p.q running) (p.alpha alpha) (p.claims claims) (p.transcript t1) env
      (observation (output p) (events env) (NNG_TreeSuffixes.f_r2 c s running alpha t1 claims))
    exact NNG_DSourceTerminal.source VL a p c s events env running alpha claims t1 runningDom hn
  | Err e =>
    change (⟨.ret (.error (p.error e)),[]⟩ : RSL.Obs (Except VL.WErr (RSL.Verified VL))) = ⟨.ret (.error (p.error e)),[]⟩
    rfl
#print axioms source
end AspisR1.NNG_DSourceClaims
