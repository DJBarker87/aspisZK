import NNG_DSourceMark2
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_DSourceRounds
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NMT_CallTree
open NNG_DProjection136 NNG_Observed136 NNG_DOccurrenceLaws136 NNG_SourceStep136 NNG_DLawStep136

theorem source (VL : RSL.VLib) (a : RSL.TX1_136.Args VL) {H W : Type}
    (p : Representation VL H) (c : Calls) (s : Parent H W)
    (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (env : RSL.Env)
    (h : Laws VL a p c s events env (NNG_TreeSuffixes.f_r c s)) :
    NNG_Canonical136.body VL a env
      (observation (output p) (events env) (NNG_TreeSuffixes.f_r c s)) := by
  let head := invoke "rounds" (s.prefixValue,s.transcript) (c.c10 s.digest s.prefixValue s.transcript)
  let k : core.result.Result (Q × Alpha × r1_wire.SemanticTranscript H) r1_wire.Error → Code (Output H) := fun r => do
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      NNG_TreeSuffixes.f_mark2 c s val.1 val.2.1 val.2.2
    | core.ops.control_flow.ControlFlow.Break residual =>
      monadLift <| core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error) residual
  have split : NNG_TreeSuffixes.f_r c s = NMT_CallTree.bind head k := rfl
  rw [split] at h ⊢
  have ent : NMT_CallTree.Event.call "rounds" (s.prefixValue,s.transcript) (c.c10 s.digest s.prefixValue s.transcript) ∈
      (run (NMT_CallTree.bind head k)).2 := entered _ _ _ _
  have headLaw : (VL.semanticRounds.run (a.prefix_,a.transcript)) env (observation (NNG_DProjection136.rounds p) (events env) head) := by
    rw [←h.rounds ent]
    exact call_actual (NNG_DProjection136.rounds p) events "rounds" (s.prefixValue,s.transcript)
      (c.c10 s.digest s.prefixValue s.transcript) env
  unfold NNG_Canonical136.body RSL.RE.bind
  refine bind_sound head k (NNG_DProjection136.rounds p) (output p) (events env) env _ _ headLaw ?_
  intro reply returned
  have next := after_return VL a p c s events env head k h reply returned
  cases reply with
  | Ok val =>
    rcases val with ⟨running,alpha,t1⟩
    have runningDom : p.qDom running := h.roundsCanonical running alpha t1 ent
      (invoke_returned (events env) "rounds" (s.prefixValue,s.transcript) _ _ returned)
    have hn : Laws VL a p c s events env (NNG_TreeSuffixes.f_mark2 c s running alpha t1) := by
      apply same_trace VL a p c s events env _ _ next
      rfl
    change NNG_Canonical136.claims VL a (p.q running) (p.alpha alpha) (p.transcript t1) env
      (observation (output p) (events env) (NNG_TreeSuffixes.f_mark2 c s running alpha t1))
    exact NNG_DSourceMark2.source VL a p c s events env running alpha t1 runningDom hn
  | Err e =>
    change (⟨.ret (.error (p.error e)),[]⟩ : RSL.Obs (Except VL.WErr (RSL.Verified VL))) = ⟨.ret (.error (p.error e)),[]⟩
    rfl
#print axioms source
end AspisR1.NNG_DSourceRounds
