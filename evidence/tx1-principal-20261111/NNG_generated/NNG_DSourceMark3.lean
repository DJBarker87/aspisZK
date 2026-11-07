import NNG_DSourceLow
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_DSourceMark3
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NMT_CallTree
open NNG_DProjection136 NNG_Observed136 NNG_DOccurrenceLaws136 NNG_SourceStep136 NNG_DLawStep136

theorem source (VL : RSL.VLib) (a : RSL.TX1_136.Args VL) {H W : Type}
    (p : Representation VL H) (c : Calls) (s : Parent H W)
    (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (env : RSL.Env)
    (running terminal : Q) (alpha : Alpha) (claims : Claims) (t1 : r1_wire.SemanticTranscript H)
    (runningDom : p.qDom running)
    (h : Laws VL a p c s events env (NNG_TreeSuffixes.f_mark3 c s running terminal alpha t1 claims)) :
    NNG_Canonical136.mask VL a (p.q running) (p.q terminal) (p.alpha alpha) (p.claims claims) (p.transcript t1) env
      (observation (output p) (events env) (NNG_TreeSuffixes.f_mark3 c s running terminal alpha t1 claims)) := by
  let head := invoke "mark3" (s.observer,3#u8) (c.c9 s.observer 3#u8)
  let k : Unit → Code (Output H) := fun _ => NNG_TreeSuffixes.f_a c s running terminal alpha t1 claims
  have split : NNG_TreeSuffixes.f_mark3 c s running terminal alpha t1 claims = NMT_CallTree.bind head k := rfl
  rw [split] at h ⊢
  have ent : NMT_CallTree.Event.call "mark3" (s.observer,3#u8) (c.c9 s.observer 3#u8) ∈
      (run (NMT_CallTree.bind head k)).2 := entered _ _ _ _
  have headLaw : RSL.Spec.pure () env (observation id (events env) head) := by
    rw [←h.mark "mark3" s.observer 3#u8 ent]
    exact call_actual id events "mark3" (s.observer,3#u8) (c.c9 s.observer 3#u8) env
  refine pure_bind_sound head k id (output p) (events env) env ()
    (fun _ => NNG_Canonical136.mask VL a (p.q running) (p.q terminal) (p.alpha alpha) (p.claims claims) (p.transcript t1)) headLaw ?_
  intro u returned
  have next := after_return VL a p c s events env head k h u returned
  cases u
  exact NNG_DSourceLow.source VL a p c s events env running terminal alpha claims t1 runningDom next
#print axioms source
end AspisR1.NNG_DSourceMark3
