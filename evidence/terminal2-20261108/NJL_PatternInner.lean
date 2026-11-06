import NJL_PatternCuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJL_PatternInner
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open NJB_PatternReference (State pattern offset coordinates)
inductive Trace (terms : Fin 14 → NQ) (weights : Fin 26 → NQ) (g : Fin 4) : List (Fin 26) → State → State → Prop
 | nil (s) : Trace terms weights g [] s s
 | cons {c cs before next last} : NJL_PatternCuts.InnerStep terms weights g c before next →
  Trace terms weights g cs next last → Trace terms weights g (c::cs) before last
theorem run (terms : Fin 14 → NQ) (weights : Fin 26 → NQ) (g : Fin 4) (xs : List (Fin 26)) (before : State)
 (range : ∀ c∈xs,offset g.castSucc≤c.val ∧ c.val<offset g.succ)
 (ht : ∀ i,Canon (terms i)) (hw : ∀ i,Canon (weights i)) (hb : ∀ i,Canon (before i)) :
 ∃ after,NJB_StateUpdates.run (fun c state=>NJB_StateUpdates.mulAdd state g (terms (pattern c)) (weights c)) xs before=ok after ∧
 Trace terms weights g xs before after ∧ (∀ i,Canon (after i)) := by
 induction xs generalizing before with
 | nil => exact ⟨before,rfl,.nil _,hb⟩
 | cons c cs ih =>
  obtain ⟨next,call,cut,hn⟩ := NJL_PatternCuts.inner_source terms weights before g c (range c (by simp)) ht hw hb
  obtain ⟨last,rest,trace,hl⟩ := ih next (fun c hc=>range c (by simp [hc])) hn
  exact ⟨last,by simp only [NJB_StateUpdates.run,call,rest,bind_tc_ok],.cons cut trace,hl⟩
/-- Exact source interval, all native inner windows consumed in order. -/
theorem source (terms : Fin 14 → NQ) (weights : Fin 26 → NQ) (g : Fin 4) (before : State)
 (ht : ∀ i,Canon (terms i)) (hw : ∀ i,Canon (weights i)) (hb : ∀ i,Canon (before i)) :
 ∃ after,NJB_PatternReference.inner terms weights g before=ok after ∧ Trace terms weights g (coordinates g) before after ∧
 (∀ i,Canon (after i)) := by
 apply run terms weights g (coordinates g) before _ ht hw hb
 intro c member
 have bound := (List.mem_filter.mp member).2
 exact of_decide_eq_true bound
#print axioms run
#print axioms source
end AspisR1.NJL_PatternInner
end
