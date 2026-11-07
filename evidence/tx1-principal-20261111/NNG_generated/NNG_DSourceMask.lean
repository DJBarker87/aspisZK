import NNG_DSourceRecord25
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_DSourceMask
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NMT_CallTree
open NNG_DProjection136 NNG_Array136 NNG_Observed136 NNG_DOccurrenceLaws136 NNG_SourceStep136 NNG_DLawStep136

theorem source (VL : RSL.VLib) (a : RSL.TX1_136.Args VL) {H W : Type}
    (p : Representation VL H) (c : Calls) (s : Parent H W)
    (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (env : RSL.Env)
    (running terminal : Q) (alpha : Alpha) (claims : Claims) (t1 : r1_wire.SemanticTranscript H)
    (runningDom : p.qDom running)
    (h : Laws VL a p c s events env (NNG_TreeSuffixes.f_mask c s running terminal (cell claims 27#usize (by decide))
      alpha t1 claims (NNG_FromFnValues136.low claims) (NNG_FromFnValues136.high claims))) :
    NNG_Canonical136.mask VL a (p.q running) (p.q terminal) (p.alpha alpha) (p.claims claims) (p.transcript t1) env
      (observation (output p) (events env) (NNG_TreeSuffixes.f_mask c s running terminal (cell claims 27#usize (by decide))
        alpha t1 claims (NNG_FromFnValues136.low claims) (NNG_FromFnValues136.high claims))) := by
  let low := NNG_FromFnValues136.low claims
  let high := NNG_FromFnValues136.high claims
  let blind := cell claims 27#usize (by decide)
  let head := invoke "mask" (low,high,blind,alpha) (c.c6 low high blind alpha)
  let k : Q → Code (Output H) := fun mask => NNG_TreeSuffixes.f_r4 c s running terminal mask alpha t1 claims
  have split : NNG_TreeSuffixes.f_mask c s running terminal blind alpha t1 claims low high = NMT_CallTree.bind head k := rfl
  rw [split] at h ⊢
  have ent : NMT_CallTree.Event.call "mask" (low,high,blind,alpha) (c.c6 low high blind alpha) ∈
      (run (NMT_CallTree.bind head k)).2 := entered _ _ _ _
  have headLaw : RSL.Spec.pure (VL.maskValue (p.claims claims) (p.alpha alpha)) env (observation p.q (events env) head) := by
    rw [←h.mask claims alpha ent]
    exact call_actual p.q events "mask" (low,high,blind,alpha) (c.c6 low high blind alpha) env
  unfold NNG_Canonical136.mask
  rw [RSL.RE.bind_pure]
  refine pure_bind_sound head k p.q (output p) (events env) env (VL.maskValue (p.claims claims) (p.alpha alpha))
    (fun mask => NNG_Canonical136.record25a VL a (p.q running) mask (p.q terminal) (p.alpha alpha) (p.claims claims) (p.transcript t1)) headLaw ?_
  intro mask returned
  have next := after_return VL a p c s events env head k h mask returned
  exact NNG_DSourceRecord25.source VL a p c s events env running terminal mask alpha claims t1 runningDom next
#print axioms source
end AspisR1.NNG_DSourceMask
