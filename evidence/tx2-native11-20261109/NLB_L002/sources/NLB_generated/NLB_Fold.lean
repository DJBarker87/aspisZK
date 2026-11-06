import NLB_State
set_option autoImplicit false
noncomputable section
namespace NLB_Parent
open Aeneas Aeneas.Std Result NKE_Free
/-- Local counterpart of NHZ_DRIVER.events_from_cuts: this caller's event
alphabet is heterogeneous and includes owned values, so its existing typed
Program/Codec is used. The induction order, failure truncation and chronological
append are identical. No execution log is an input to G. -/
theorem events_from_cuts {A : Type} (window : Event → Event)
 (p : Program Event A) (before : List Event)
 (steps : ∀ e∈(eval p).events, window e=e) :
 G window p before=.done (eval p).result (before++(eval p).events) := by
 induction p generalizing before with
 | ret value => simp only [G,eval,List.append_nil]
 | prim actual next ih =>
  cases actual with
  | fail error => simp only [G,eval,List.append_nil]
  | div => simp only [G,eval,List.append_nil]
  | ok value => exact ih value before steps
 | call codec seed next ih =>
  have localStep : window (codec.encode seed)=codec.encode seed := by
   apply steps
   cases seed <;> simp only [eval,List.mem_cons,List.mem_singleton] <;> exact Or.inl rfl
  cases seed with
  | fail error => simp only [G,localStep,codec.roundtrip,eval]
  | div => simp only [G,localStep,codec.roundtrip,eval]
  | ok value =>
   simp only [G,localStep,codec.roundtrip]
   rw [ih value]
   · simp only [eval,List.append_assoc,List.singleton_append]
   · intro e he
     exact steps e (List.mem_cons_of_mem _ he)
#print axioms events_from_cuts
end NLB_Parent
