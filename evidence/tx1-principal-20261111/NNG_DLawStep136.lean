import NNG_DOccurrenceLaws136
import NNG_LawStep136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_DLawStep136
open Aeneas Aeneas.Std Result NMT_CallTree NNG_Emitted NNG_Observed136
open NNG_DProjection136 NNG_DOccurrenceLaws136 NNG_SourceStep136
export NNG_LawStep136 (invoke_member entered call_actual pure_bind_sound silent_result pure_value)
#print axioms invoke_member
#print axioms entered
#print axioms call_actual
#print axioms pure_bind_sound
#print axioms silent_result
#print axioms pure_value

theorem after_return (VL : RSL.VLib) (arg : RSL.TX1_136.Args VL) {H W A B : Type}
    (p : Representation VL H) (c : Calls) (s : Parent H W)
    (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (env : RSL.Env)
    (head : Code A) (k : A → Code B) (h : Laws VL arg p c s events env (NMT_CallTree.bind head k)) (a : A)
    (returned : (observation id (events env) head).exit = .ret a) : Laws VL arg p c s events env (k a) :=
  restrict VL arg p c s events env _ _ h
    (within_tail head k a (returned_run (events env) head a returned))
#print axioms after_return

theorem same_trace (VL : RSL.VLib) (arg : RSL.TX1_136.Args VL) {H W A B : Type}
    (p : Representation VL H) (c : Calls) (s : Parent H W)
    (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (env : RSL.Env)
    (whole : Code A) (part : Code B) (h : Laws VL arg p c s events env whole)
    (trace : (run part).2 = (run whole).2) : Laws VL arg p c s events env part := by
  apply restrict VL arg p c s events env whole part h
  intro e he
  rw [←trace]
  exact he
#print axioms same_trace

theorem invoke_returned {Args A : Type} (events : NMT_CallTree.Event → List RSL.Event)
    (site : String) (args : Args) (r : Result A) (a : A)
    (returned : (observation id events (invoke site args r)).exit = .ret a) : r = .ok a := by
  have h := returned_run events (invoke site args r) a returned
  rw [run_result,erase_invoke] at h
  exact h
#print axioms invoke_returned
end AspisR1.NNG_DLawStep136
