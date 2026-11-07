import NNG_DSourceBeforeZ1
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_DSourceRecord26
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NMT_CallTree
open NNG_DProjection136 NNG_Observed136 NNG_DOccurrenceLaws136 NNG_SourceStep136 NNG_DLawStep136

theorem source (VL : RSL.VLib) (a : RSL.TX1_136.Args VL) {H W : Type}
    (p : Representation VL H) (c : Calls) (s : Parent H W)
    (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (env : RSL.Env)
    (alpha : Alpha) (claims : Claims) (extra : K29) (state : Array U8 32#usize)
    (z0 : aspis_core.circle.SecureCirclePoint) (t2 : r1_wire.SemanticTranscript H)
    (h : Laws VL a p c s events env (NNG_TreeSuffixes.f_r7 c s alpha claims extra state t2 z0)) :
    NNG_Canonical136.record26a VL a (p.alpha alpha) (p.claims claims) (p.k29 extra)
      (p.b32 state) (p.point z0) (p.transcript t2) env
      (observation (output p) (events env) (NNG_TreeSuffixes.f_r7 c s alpha claims extra state t2 z0)) := by
  let head := invoke "record26" (s.prefixValue,26#u8) (c.c11 s.prefixValue 26#u8)
  let k : core.result.Result r1_wire.ValidatedRecord r1_wire.Error → Code (Output H) := fun r7 => do
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r7
    match cf with
    | core.ops.control_flow.ControlFlow.Continue rec26 =>
      NNG_TreeSuffixes.f_r8 c s alpha claims extra state t2 z0 rec26 r7
    | core.ops.control_flow.ControlFlow.Break residual =>
      monadLift <| core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error) residual
  have split : NNG_TreeSuffixes.f_r7 c s alpha claims extra state t2 z0 = NMT_CallTree.bind head k := rfl
  rw [split] at h ⊢
  have ent : NMT_CallTree.Event.call "record26" (s.prefixValue,26#u8) (c.c11 s.prefixValue 26#u8) ∈
      (run (NMT_CallTree.bind head k)).2 := entered _ _ _ _
  have headLaw : (RSL.RE.ofExcept (VL.validatedRecord a.prefix_ 26)) env
      (observation (recordReply p) (events env) head) := by
    rw [←h.record26 ent]
    exact call_actual (recordReply p) events "record26" (s.prefixValue,26#u8) (c.c11 s.prefixValue 26#u8) env
  unfold NNG_Canonical136.record26a RSL.RE.bind
  refine bind_sound head k (recordReply p) (output p) (events env) env _ _ headLaw ?_
  intro reply returned
  have next := after_return VL a p c s events env head k h reply returned
  have remembered := pure_value (recordReply p) head (events env) env (VL.validatedRecord a.prefix_ 26) reply headLaw returned
  cases reply with
  | Ok rec26 =>
    have saved : VL.validatedRecord a.prefix_ 26 = .ok (p.record rec26) := remembered.symm
    have hn : Laws VL a p c s events env (NNG_TreeSuffixes.f_r8 c s alpha claims extra state t2 z0 rec26 (.Ok rec26)) := by
      apply same_trace VL a p c s events env _ _ next
      rfl
    change NNG_Canonical136.beforeZ1 VL a (p.alpha alpha) (p.claims claims) (p.k29 extra)
      (p.b32 state) (p.point z0) (p.transcript t2) (p.record rec26) env
      (observation (output p) (events env) (NNG_TreeSuffixes.f_r8 c s alpha claims extra state t2 z0 rec26 (.Ok rec26)))
    exact NNG_DSourceBeforeZ1.source VL a p c s events env alpha claims extra state z0 t2 rec26 saved hn
  | Err e =>
    change (⟨.ret (.error (p.error e)),[]⟩ : RSL.Obs (Except VL.WErr (RSL.Verified VL))) = ⟨.ret (.error (p.error e)),[]⟩
    rfl
#print axioms source
end AspisR1.NNG_DSourceRecord26
