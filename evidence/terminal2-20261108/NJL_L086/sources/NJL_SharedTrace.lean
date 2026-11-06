import NJL_SharedCuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJL_SharedTrace
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open NJL_SharedCuts (State)
inductive Trace (values : Fin 33 → NQ) (selector : NQ) : List (Fin 9) → State → State → Prop
 | nil (s : State) : Trace values selector [] s s
 | cons {g gs before middle after} (first : NJL_SharedCuts.Step values selector g before middle)
   (rest : Trace values selector gs middle after) : Trace values selector (g::gs) before after
/-- Nine source-ordered groups12..20, established by NJB_K052/K053;
one arbitrary prestate native step, then finite Lean induction. -/
theorem source (values : Fin 33 → NQ) (selector : NQ) (groups : List (Fin 9)) (before : State)
 (hv : ∀ i,Canon (values i)) (hc : Canon selector) (hb : ∀ i,Canon (before i)) :
 ∃ after,NJB_StateUpdates.run (NJB_SharedReference.step values selector) groups before=ok after ∧
 Trace values selector groups before after ∧ (∀ i,Canon (after i)) := by
 induction groups generalizing before with
 | nil => exact ⟨before,rfl,.nil before,hb⟩
 | cons g gs ih =>
  obtain ⟨middle,cm,tm,hm⟩ := NJL_SharedCuts.source values selector g before hv hc hb
  obtain ⟨after,ca,ta,ha⟩ := ih middle hm
  refine ⟨after,?_,.cons tm ta,ha⟩
  simp only [NJB_StateUpdates.run,cm,ca,bind_tc_ok]
#print source
#print axioms source
end AspisR1.NJL_SharedTrace
end
