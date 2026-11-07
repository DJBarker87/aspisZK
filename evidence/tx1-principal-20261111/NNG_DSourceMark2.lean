import NNG_DSourceClaims
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_DSourceMark2
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NMT_CallTree
open NNG_DProjection136 NNG_Observed136 NNG_DOccurrenceLaws136 NNG_SourceStep136 NNG_DLawStep136

theorem source (VL : RSL.VLib) (a : RSL.TX1_136.Args VL) {H W : Type}
    (p : Representation VL H) (c : Calls) (s : Parent H W)
    (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (env : RSL.Env)
    (running : Q) (alpha : Alpha) (t1 : r1_wire.SemanticTranscript H)
    (runningDom : p.qDom running)
    (h : Laws VL a p c s events env (NNG_TreeSuffixes.f_mark2 c s running alpha t1)) :
    NNG_Canonical136.claims VL a (p.q running) (p.alpha alpha) (p.transcript t1) env
      (observation (output p) (events env) (NNG_TreeSuffixes.f_mark2 c s running alpha t1)) := by
  let head := invoke "mark2" (s.observer,2#u8) (c.c9 s.observer 2#u8)
  let k : Unit → Code (Output H) := fun _ => NNG_TreeSuffixes.f_r1 c s running alpha t1
  have split : NNG_TreeSuffixes.f_mark2 c s running alpha t1 = NMT_CallTree.bind head k := rfl
  rw [split] at h ⊢
  have ent : NMT_CallTree.Event.call "mark2" (s.observer,2#u8) (c.c9 s.observer 2#u8) ∈
      (run (NMT_CallTree.bind head k)).2 := entered _ _ _ _
  have headLaw : RSL.Spec.pure () env (observation id (events env) head) := by
    rw [←h.mark "mark2" s.observer 2#u8 ent]
    exact call_actual id events "mark2" (s.observer,2#u8) (c.c9 s.observer 2#u8) env
  refine pure_bind_sound head k id (output p) (events env) env ()
    (fun _ => NNG_Canonical136.claims VL a (p.q running) (p.alpha alpha) (p.transcript t1)) headLaw ?_
  intro u returned
  have next := after_return VL a p c s events env head k h u returned
  cases u
  exact NNG_DSourceClaims.source VL a p c s events env running alpha t1 runningDom next
#print axioms source
end AspisR1.NNG_DSourceMark2
