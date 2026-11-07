import NNG_DSourceTerminalGuard
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_DSourceAddExtra
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NMT_CallTree
open NNG_DProjection136 NNG_Array136 NNG_Observed136 NNG_DOccurrenceLaws136 NNG_SourceStep136 NNG_DLawStep136

theorem source (VL : RSL.VLib) (a : RSL.TX1_136.Args VL) {H W : Type}
    (p : Representation VL H) (c : Calls) (s : Parent H W)
    (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (env : RSL.Env)
    (running partialValue : Q) (alpha : Alpha) (claims : Claims) (extra : K29)
    (t1 : r1_wire.SemanticTranscript H) (rec25 : r1_wire.ValidatedRecord) (runningDom : p.qDom running)
    (saved : VL.validatedRecord a.prefix_ 25 = .ok (p.record rec25))
    (h : Laws VL a p c s events env (NNG_TreeSuffixes.f_masked_terminal c s running partialValue
      (get extra 28#usize (by decide)) alpha t1 claims extra (.Ok rec25))) :
    NNG_Canonical136.addExtra VL a (p.q running) (p.q partialValue) (p.alpha alpha) (p.claims claims) (p.k29 extra) (p.transcript t1) env
      (observation (output p) (events env) (NNG_TreeSuffixes.f_masked_terminal c s running partialValue
        (get extra 28#usize (by decide)) alpha t1 claims extra (.Ok rec25))) := by
  let q3 := get extra 28#usize (by decide)
  let head := invoke "addExtra" (partialValue,q3) (c.c4 partialValue q3)
  let k : Q → Code (Output H) := fun masked => NNG_TreeSuffixes.f_b c s running masked alpha t1 claims extra (.Ok rec25)
  have split : NNG_TreeSuffixes.f_masked_terminal c s running partialValue q3 alpha t1 claims extra (.Ok rec25) =
      NMT_CallTree.bind head k := rfl
  change _ env (observation (output p) (events env) (NNG_TreeSuffixes.f_masked_terminal c s running partialValue q3 alpha t1 claims extra (.Ok rec25)))
  rw [split] at h ⊢
  have ent : NMT_CallTree.Event.call "addExtra" (partialValue,q3) (c.c4 partialValue q3) ∈
      (run (NMT_CallTree.bind head k)).2 := entered _ _ _ _
  have headLaw : RSL.Spec.pure (VL.qadd (p.q partialValue) (p.q q3)) env (observation p.q (events env) head) := by
    rw [←h.addExtra partialValue q3 ent]
    exact call_actual p.q events "addExtra" (partialValue,q3) (c.c4 partialValue q3) env
  unfold NNG_Canonical136.addExtra
  rw [RSL.RE.bind_pure,p.at28]
  refine pure_bind_sound head k p.q (output p) (events env) env (VL.qadd (p.q partialValue) (p.q q3))
    (fun masked => NNG_Canonical136.terminalGuard VL a (p.q running) masked (p.alpha alpha) (p.claims claims) (p.k29 extra) (p.transcript t1)) headLaw ?_
  intro masked returned
  have next := after_return VL a p c s events env head k h masked returned
  have maskedDom : p.qDom masked := h.addExtraCanonical partialValue q3 ent masked
    (invoke_returned (events env) "addExtra" (partialValue,q3) (c.c4 partialValue q3) masked returned)
  exact NNG_DSourceTerminalGuard.source VL a p c s events env running masked alpha claims extra t1 rec25 runningDom maskedDom saved next
#print axioms source
end AspisR1.NNG_DSourceAddExtra
