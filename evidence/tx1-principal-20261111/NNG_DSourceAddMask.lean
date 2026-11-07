import NNG_DSourceIndex28
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_DSourceAddMask
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NMT_CallTree
open NNG_DProjection136 NNG_Observed136 NNG_DOccurrenceLaws136 NNG_SourceStep136 NNG_DLawStep136

theorem source (VL : RSL.VLib) (a : RSL.TX1_136.Args VL) {H W : Type}
    (p : Representation VL H) (c : Calls) (s : Parent H W)
    (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (env : RSL.Env)
    (running mask product : Q) (alpha : Alpha) (claims : Claims) (extra : K29)
    (t1 : r1_wire.SemanticTranscript H) (rec25 : r1_wire.ValidatedRecord) (runningDom : p.qDom running)
    (saved : VL.validatedRecord a.prefix_ 25 = .ok (p.record rec25))
    (h : Laws VL a p c s events env (NNG_TreeSuffixes.f_q2 c s running mask product alpha t1 claims extra (.Ok rec25))) :
    NNG_Canonical136.addMask VL a (p.q running) (p.q mask) (p.q product) (p.alpha alpha) (p.claims claims) (p.k29 extra) (p.transcript t1) env
      (observation (output p) (events env) (NNG_TreeSuffixes.f_q2 c s running mask product alpha t1 claims extra (.Ok rec25))) := by
  let head := invoke "addMask" (mask,product) (c.c4 mask product)
  let k : Q → Code (Output H) := fun partialValue => NNG_TreeSuffixes.f_q3 c s running partialValue alpha t1 claims extra (.Ok rec25)
  have split : NNG_TreeSuffixes.f_q2 c s running mask product alpha t1 claims extra (.Ok rec25) = NMT_CallTree.bind head k := rfl
  rw [split] at h ⊢
  have ent : NMT_CallTree.Event.call "addMask" (mask,product) (c.c4 mask product) ∈
      (run (NMT_CallTree.bind head k)).2 := entered _ _ _ _
  have headLaw : RSL.Spec.pure (VL.qadd (p.q mask) (p.q product)) env (observation p.q (events env) head) := by
    rw [←h.addMask mask product ent]
    exact call_actual p.q events "addMask" (mask,product) (c.c4 mask product) env
  unfold NNG_Canonical136.addMask
  rw [RSL.RE.bind_pure]
  refine pure_bind_sound head k p.q (output p) (events env) env (VL.qadd (p.q mask) (p.q product))
    (fun partialValue => NNG_Canonical136.addExtra VL a (p.q running) partialValue (p.alpha alpha) (p.claims claims) (p.k29 extra) (p.transcript t1)) headLaw ?_
  intro partialValue returned
  have next := after_return VL a p c s events env head k h partialValue returned
  exact NNG_DSourceIndex28.source VL a p c s events env running partialValue alpha claims extra t1 rec25 runningDom saved next
#print axioms source
end AspisR1.NNG_DSourceAddMask
