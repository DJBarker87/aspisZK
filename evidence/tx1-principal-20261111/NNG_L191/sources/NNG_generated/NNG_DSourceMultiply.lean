import NNG_DSourceAddMask
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_DSourceMultiply
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NMT_CallTree
open NNG_DProjection136 NNG_Observed136 NNG_DOccurrenceLaws136 NNG_SourceStep136 NNG_DLawStep136

theorem source (VL : RSL.VLib) (a : RSL.TX1_136.Args VL) {H W : Type}
    (p : Representation VL H) (c : Calls) (s : Parent H W)
    (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (env : RSL.Env)
    (running terminal mask : Q) (alpha : Alpha) (claims : Claims) (extra : K29)
    (t1 : r1_wire.SemanticTranscript H) (rec25 : r1_wire.ValidatedRecord) (runningDom : p.qDom running)
    (saved : VL.validatedRecord a.prefix_ 25 = .ok (p.record rec25))
    (h : Laws VL a p c s events env (NNG_TreeSuffixes.f_q1 c s running terminal mask alpha t1 claims extra (.Ok rec25))) :
    NNG_Canonical136.multiply VL a (p.q running) (p.q mask) (p.q terminal) (p.alpha alpha) (p.claims claims) (p.k29 extra) (p.transcript t1) env
      (observation (output p) (events env) (NNG_TreeSuffixes.f_q1 c s running terminal mask alpha t1 claims extra (.Ok rec25))) := by
  let head := invoke "multiply" (s.challenges.eta,terminal) (c.c5 s.challenges.eta terminal)
  let k : Q → Code (Output H) := fun product => NNG_TreeSuffixes.f_q2 c s running mask product alpha t1 claims extra (.Ok rec25)
  have split : NNG_TreeSuffixes.f_q1 c s running terminal mask alpha t1 claims extra (.Ok rec25) = NMT_CallTree.bind head k := rfl
  rw [split] at h ⊢
  have ent : NMT_CallTree.Event.call "multiply" (s.challenges.eta,terminal) (c.c5 s.challenges.eta terminal) ∈
      (run (NMT_CallTree.bind head k)).2 := entered _ _ _ _
  have headLaw : RSL.Spec.pure (VL.qmul (p.q s.challenges.eta) (p.q terminal)) env (observation p.q (events env) head) := by
    rw [←h.multiply s.challenges.eta terminal ent]
    exact call_actual p.q events "multiply" (s.challenges.eta,terminal) (c.c5 s.challenges.eta terminal) env
  unfold NNG_Canonical136.multiply
  rw [RSL.RE.bind_pure,h.inputs.eta]
  refine pure_bind_sound head k p.q (output p) (events env) env (VL.qmul (p.q s.challenges.eta) (p.q terminal))
    (fun product => NNG_Canonical136.addMask VL a (p.q running) (p.q mask) product (p.alpha alpha) (p.claims claims) (p.k29 extra) (p.transcript t1)) headLaw ?_
  intro product returned
  have next := after_return VL a p c s events env head k h product returned
  exact NNG_DSourceAddMask.source VL a p c s events env running mask product alpha claims extra t1 rec25 runningDom saved next
#print axioms source
end AspisR1.NNG_DSourceMultiply
