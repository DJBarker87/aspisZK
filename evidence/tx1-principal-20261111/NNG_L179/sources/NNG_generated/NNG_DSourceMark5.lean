import NNG_DSourceCircleGuard136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_DSourceMark5
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NMT_CallTree
open NNG_DProjection136 NNG_Observed136 NNG_DOccurrenceLaws136 NNG_SourceStep136 NNG_DLawStep136

theorem source (VL : RSL.VLib) (a : RSL.TX1_136.Args VL) {H W : Type}
    (p : Representation VL H) (c : Calls) (s : Parent H W)
    (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (env : RSL.Env)
    (alpha : Alpha) (claims : Claims) (extra before : K29) (state : Array U8 32#usize)
    (z0 z1 : aspis_core.circle.SecureCirclePoint) (t3 : r1_wire.SemanticTranscript H)
    (h : Laws VL a p c s events env (NNG_TreeSuffixes.f_mark5 c s alpha claims extra state z0 before t3 z1)) :
    NNG_Canonical136.circleGuard VL a (p.alpha alpha) (p.claims claims) (p.k29 extra) (p.k29 before)
      (p.b32 state) (p.point z0) (p.point z1) (p.transcript t3) env
      (observation (output p) (events env)
        (NNG_TreeSuffixes.f_mark5 c s alpha claims extra state z0 before t3 z1)) := by
  let head := invoke "mark5" (s.observer,5#u8) (c.c9 s.observer 5#u8)
  let k : Unit → Code (Output H) := fun _ => NNG_TreeSuffixes.f_b1 c s alpha claims extra state z0 before t3 z1
  have split : NNG_TreeSuffixes.f_mark5 c s alpha claims extra state z0 before t3 z1 =
      NMT_CallTree.bind head k := rfl
  rw [split] at h ⊢
  have ent : NMT_CallTree.Event.call "mark5" (s.observer,5#u8) (c.c9 s.observer 5#u8) ∈
      (run (NMT_CallTree.bind head k)).2 := entered _ _ _ _
  have headLaw : RSL.Spec.pure () env (observation id (events env) head) := by
    rw [←h.mark "mark5" s.observer 5#u8 ent]
    exact call_actual id events "mark5" (s.observer,5#u8) (c.c9 s.observer 5#u8) env
  refine pure_bind_sound head k id (output p) (events env) env ()
    (fun _ => NNG_Canonical136.circleGuard VL a (p.alpha alpha) (p.claims claims) (p.k29 extra) (p.k29 before)
      (p.b32 state) (p.point z0) (p.point z1) (p.transcript t3)) headLaw ?_
  intro u returned
  have next := after_return VL a p c s events env head k h u returned
  cases u
  exact NNG_DSourceCircleGuard136.source VL a p c s events env alpha claims extra before state z0 z1 t3 next
#print axioms source
end AspisR1.NNG_DSourceMark5
