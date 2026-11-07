import NNG_DSourceState136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_DSourceMark4
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NMT_CallTree
open NNG_DProjection136 NNG_Observed136 NNG_DOccurrenceLaws136 NNG_SourceStep136 NNG_DLawStep136

theorem source (VL : RSL.VLib) (a : RSL.TX1_136.Args VL) {H W : Type}
    (p : Representation VL H) (c : Calls) (s : Parent H W)
    (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (env : RSL.Env)
    (alpha : Alpha) (claims : Claims) (extra : K29) (t1 : r1_wire.SemanticTranscript H) (rec25 : r1_wire.ValidatedRecord)
    (saved : VL.validatedRecord a.prefix_ 25 = .ok (p.record rec25))
    (h : Laws VL a p c s events env (NNG_TreeSuffixes.f_mark4 c s alpha t1 claims extra (.Ok rec25))) :
    NNG_Canonical136.stateBefore VL a (p.alpha alpha) (p.claims claims) (p.k29 extra) (p.transcript t1) env
      (observation (output p) (events env) (NNG_TreeSuffixes.f_mark4 c s alpha t1 claims extra (.Ok rec25))) := by
  let head := invoke "mark4" (s.observer,4#u8) (c.c9 s.observer 4#u8)
  let k : Unit → Code (Output H) := fun _ => NNG_TreeSuffixes.f_state_before_z0 c s alpha t1 claims extra (.Ok rec25)
  have split : NNG_TreeSuffixes.f_mark4 c s alpha t1 claims extra (.Ok rec25) = NMT_CallTree.bind head k := rfl
  rw [split] at h ⊢
  have ent : NMT_CallTree.Event.call "mark4" (s.observer,4#u8) (c.c9 s.observer 4#u8) ∈
      (run (NMT_CallTree.bind head k)).2 := entered _ _ _ _
  have headLaw : RSL.Spec.pure () env (observation id (events env) head) := by
    rw [←h.mark "mark4" s.observer 4#u8 ent]
    exact call_actual id events "mark4" (s.observer,4#u8) (c.c9 s.observer 4#u8) env
  refine pure_bind_sound head k id (output p) (events env) env ()
    (fun _ => NNG_Canonical136.stateBefore VL a (p.alpha alpha) (p.claims claims) (p.k29 extra) (p.transcript t1)) headLaw ?_
  intro u returned
  have next := after_return VL a p c s events env head k h u returned
  cases u
  exact NNG_DSourceState136.source VL a p c s events env alpha claims extra t1 rec25 saved next
#print axioms source
end AspisR1.NNG_DSourceMark4
