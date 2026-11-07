import NNG_OccurrenceLaws136
import NNG_EmittedCallGraph
import NNG_EmittedPureCall
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_LawStep136
open Aeneas Aeneas.Std Result NMT_CallTree NNG_Emitted NNG_Observed136 NNG_ObservationAlgebra
open NNG_InterpretProjection NNG_SourceStep136 NNG_OccurrenceLaws136 NNG_Projection136 NNG_EmittedCallGraph

theorem invoke_member {Args A : Type} (site : String) (args : Args) (r : Result A) :
    NMT_CallTree.Event.call site args r ∈ (run (invoke site args r)).2 := by
  cases r <;> exact List.mem_cons_self
#print axioms invoke_member

theorem entered {Args A B : Type} (site : String) (args : Args) (r : Result A) (k : A → Code B) :
    NMT_CallTree.Event.call site args r ∈ (run (NMT_CallTree.bind (invoke site args r) k)).2 :=
  within_head (invoke site args r) k _ (invoke_member site args r)
#print axioms entered

theorem call_actual {Args A B : Type} (decode : A → B)
    (events : RSL.Env → NMT_CallTree.Event → List RSL.Event)
    (site : String) (args : Args) (r : Result A) (env : RSL.Env) :
    RSL.Spec.map decode (NNG_Interpret136.call events site args r) env
      (observation decode (events env) (invoke site args r)) := by
  rw [call_projection]
  change observation decode (events env) (invoke site args r) =
    ⟨exit decode r,events env (.call site args r)⟩
  cases r <;> simp only [observation,invoke,run,exit,id_eq,List.flatMap_cons,List.flatMap_nil,List.append_nil]
#print axioms call_actual

theorem after_return (VL : RSL.VLib) {H W A B : Type} (p : Representation VL H)
    (c : Calls) (s : Parent H W) (events : RSL.Env → NMT_CallTree.Event → List RSL.Event)
    (env : RSL.Env) (head : Code A) (k : A → Code B)
    (h : Laws VL p c s events env (NMT_CallTree.bind head k)) (a : A)
    (returned : (observation id (events env) head).exit = .ret a) :
    Laws VL p c s events env (k a) :=
  restrict VL p c s events env _ _ h
    (within_tail head k a (returned_run (events env) head a returned))
#print axioms after_return

theorem same_trace (VL : RSL.VLib) {H W A B : Type} (p : Representation VL H)
    (c : Calls) (s : Parent H W) (events : RSL.Env → NMT_CallTree.Event → List RSL.Event)
    (env : RSL.Env) (whole : Code A) (part : Code B) (h : Laws VL p c s events env whole)
    (trace : (run part).2 = (run whole).2) : Laws VL p c s events env part := by
  apply restrict VL p c s events env whole part h
  intro e he
  rw [←trace]
  exact he
#print axioms same_trace

theorem pure_bind_sound {A B C D : Type}
    (head : Code A) (k : A → Code B) (headDecode : A → C) (outDecode : B → D)
    (events : NMT_CallTree.Event → List RSL.Event) (env : RSL.Env) (value : C)
    (tail : C → RSL.Spec D)
    (headLaw : RSL.Spec.pure value env (observation headDecode events head))
    (tailLaw : ∀ a, (observation id events head).exit = .ret a →
      tail (headDecode a) env (observation outDecode events (k a))) :
    tail value env (observation outDecode events (NMT_CallTree.bind head k)) := by
  have step := bind_sound head k headDecode outDecode events env (RSL.Spec.pure value) tail headLaw tailLaw
  rw [RSL.Spec.bind_pure] at step
  exact step
#print axioms pure_bind_sound

theorem silent_result {A B : Type} (decode : A → B) (r : Result A) (value : B)
    (events : NMT_CallTree.Event → List RSL.Event) (source : resultMap decode r = .ok value) :
    observation decode events (liftM r : Code A) = ⟨.ret value, []⟩ := by
  cases r with
  | ok a =>
    change (⟨.ret (decode a),[]⟩ : RSL.Obs B) = ⟨.ret value,[]⟩
    exact congrArg (fun x => (⟨.ret x,[]⟩ : RSL.Obs B)) (Result.ok.inj source)
  | fail e => cases source
  | div => cases source
#print axioms silent_result
theorem pure_value {A B : Type} (decode : A → B) (code : Code A)
    (events : NMT_CallTree.Event → List RSL.Event) (env : RSL.Env) (value : B) (a : A)
    (headLaw : RSL.Spec.pure value env (observation decode events code))
    (returned : (observation id events code).exit = .ret a) : decode a = value := by
  change observation decode events code = ⟨.ret value,[]⟩ at headLaw
  have mapped : (observation decode events code).exit = .ret (decode a) := by
    rw [←map_observation decode events code]
    change mapExit decode (observation id events code).exit = .ret (decode a)
    rw [returned]
    rfl
  exact RSL.Exit.ret.inj (mapped.symm.trans (congrArg RSL.Obs.exit headLaw))
#print axioms pure_value
end AspisR1.NNG_LawStep136
