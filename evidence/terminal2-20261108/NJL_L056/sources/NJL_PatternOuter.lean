import NJL_PatternInner
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJL_PatternOuter
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open NJB_PatternReference (State offset coordinates)
/-- One actual inner invocation and its native outer cut. All four child
post-state cells and their frame are supplied by the derived inner trace. -/
def Group (terms : Fin 14 → NQ) (weights : Fin 26 → NQ) (g : Fin 4) (before after : State) : Prop :=
 NJB_PatternReference.inner terms weights g before=ok after ∧
 NJL_PatternInner.Trace terms weights g (coordinates g) before after ∧
 NJL_PatternCuts.outer terms weights before g after after before weights terms 1 g.val
  (offset g.castSucc) (offset g.succ) (g.val+1)
theorem group_source (terms : Fin 14 → NQ) (weights : Fin 26 → NQ) (g : Fin 4) (before : State)
 (ht : ∀ i,Canon (terms i)) (hw : ∀ i,Canon (weights i)) (hb : ∀ i,Canon (before i)) :
 ∃ after,Group terms weights g before after ∧ (∀ i,Canon (after i)) := by
 obtain ⟨after,call,trace,ha⟩ := NJL_PatternInner.source terms weights g before ht hw hb
 exact ⟨after,⟨call,trace,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,fun _=>rfl⟩,ha⟩
inductive Trace (terms : Fin 14 → NQ) (weights : Fin 26 → NQ) : List (Fin 4) → State → State → Prop
 | nil (s) : Trace terms weights [] s s
 | cons {g gs before next last} : Group terms weights g before next → Trace terms weights gs next last →
  Trace terms weights (g::gs) before last
theorem run (terms : Fin 14 → NQ) (weights : Fin 26 → NQ) (gs : List (Fin 4)) (before : State)
 (ht : ∀ i,Canon (terms i)) (hw : ∀ i,Canon (weights i)) (hb : ∀ i,Canon (before i)) :
 ∃ after,NJB_StateUpdates.run (fun g s=>NJB_PatternReference.inner terms weights g s) gs before=ok after ∧
 Trace terms weights gs before after ∧ (∀ i,Canon (after i)) := by
 induction gs generalizing before with
 | nil => exact ⟨before,rfl,.nil _,hb⟩
 | cons g gs ih =>
  obtain ⟨next,cut,hn⟩ := group_source terms weights g before ht hw hb
  obtain ⟨last,rest,trace,hl⟩ := ih next hn
  exact ⟨last,by simp only [NJB_StateUpdates.run,cut.1,rest,bind_tc_ok],.cons cut trace,hl⟩
/-- Both finite loop levels and all mutable state are threaded from the SAME
initial state; the complete reference Result is an output, not a hypothesis. -/
theorem source (terms : Fin 14 → NQ) (weights : Fin 26 → NQ) (before : State)
 (ht : ∀ i,Canon (terms i)) (hw : ∀ i,Canon (weights i)) (hb : ∀ i,Canon (before i)) :
 ∃ after,NJB_PatternReference.reference terms weights before=ok after ∧
 Trace terms weights (List.ofFn (fun g : Fin 4=>g)) before after ∧ (∀ i,Canon (after i)) :=
 run terms weights _ before ht hw hb
#print axioms group_source
#print axioms run
#print axioms source
end AspisR1.NJL_PatternOuter
end
