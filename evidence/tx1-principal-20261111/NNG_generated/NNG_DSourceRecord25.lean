import NNG_DSourceExtra
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_DSourceRecord25
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NMT_CallTree
open NNG_DProjection136 NNG_Observed136 NNG_DOccurrenceLaws136 NNG_SourceStep136 NNG_DLawStep136

theorem source (VL : RSL.VLib) (a : RSL.TX1_136.Args VL) {H W : Type}
    (p : Representation VL H) (c : Calls) (s : Parent H W)
    (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (env : RSL.Env)
    (running terminal mask : Q) (alpha : Alpha) (claims : Claims) (t1 : r1_wire.SemanticTranscript H)
    (runningDom : p.qDom running)
    (h : Laws VL a p c s events env (NNG_TreeSuffixes.f_r4 c s running terminal mask alpha t1 claims)) :
    NNG_Canonical136.record25a VL a (p.q running) (p.q mask) (p.q terminal) (p.alpha alpha) (p.claims claims) (p.transcript t1) env
      (observation (output p) (events env) (NNG_TreeSuffixes.f_r4 c s running terminal mask alpha t1 claims)) := by
  let head := invoke "record25" (s.prefixValue,25#u8) (c.c11 s.prefixValue 25#u8)
  let k : core.result.Result r1_wire.ValidatedRecord r1_wire.Error → Code (Output H) := fun r4 => do
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r4
    match cf with
    | core.ops.control_flow.ControlFlow.Continue rec25 =>
      NNG_TreeSuffixes.f_r5 c s running terminal mask alpha t1 claims rec25 r4
    | core.ops.control_flow.ControlFlow.Break residual =>
      monadLift <| core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error) residual
  have split : NNG_TreeSuffixes.f_r4 c s running terminal mask alpha t1 claims = NMT_CallTree.bind head k := rfl
  rw [split] at h ⊢
  have ent : NMT_CallTree.Event.call "record25" (s.prefixValue,25#u8) (c.c11 s.prefixValue 25#u8) ∈
      (run (NMT_CallTree.bind head k)).2 := entered _ _ _ _
  have headLaw : (RSL.RE.ofExcept (VL.validatedRecord a.prefix_ 25)) env
      (observation (recordReply p) (events env) head) := by
    rw [←h.record25 ent]
    exact call_actual (recordReply p) events "record25" (s.prefixValue,25#u8) (c.c11 s.prefixValue 25#u8) env
  unfold NNG_Canonical136.record25a RSL.RE.bind
  refine bind_sound head k (recordReply p) (output p) (events env) env _ _ headLaw ?_
  intro reply returned
  have next := after_return VL a p c s events env head k h reply returned
  have remembered := pure_value (recordReply p) head (events env) env (VL.validatedRecord a.prefix_ 25) reply headLaw returned
  cases reply with
  | Ok rec25 =>
    have saved : VL.validatedRecord a.prefix_ 25 = .ok (p.record rec25) := remembered.symm
    have hn : Laws VL a p c s events env (NNG_TreeSuffixes.f_r5 c s running terminal mask alpha t1 claims rec25 (.Ok rec25)) := by
      apply same_trace VL a p c s events env _ _ next
      rfl
    change NNG_Canonical136.extra VL a (p.q running) (p.q mask) (p.q terminal) (p.alpha alpha) (p.claims claims) (p.transcript t1) (p.record rec25) env
      (observation (output p) (events env) (NNG_TreeSuffixes.f_r5 c s running terminal mask alpha t1 claims rec25 (.Ok rec25)))
    exact NNG_DSourceExtra.source VL a p c s events env running terminal mask alpha claims t1 rec25 runningDom saved hn
  | Err e =>
    change (⟨.ret (.error (p.error e)),[]⟩ : RSL.Obs (Except VL.WErr (RSL.Verified VL))) = ⟨.ret (.error (p.error e)),[]⟩
    rfl
#print axioms source
end AspisR1.NNG_DSourceRecord25
