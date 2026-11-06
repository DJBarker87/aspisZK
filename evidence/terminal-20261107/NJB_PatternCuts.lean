import NJB_PatternReference
import NJB_Cuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJB_PatternCuts
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open NJB_PatternReference (State pattern offset)
/-- NJB_pattern_inner's assumptions and assertions, with the four-limb codec
already proved in NJB_Words. No field reply is interpreted by this cut. -/
def inner (terms : Fin 14 → NQ) (weights : Fin 26 → NQ) (before : State)
 (g : Fin 4) (c : Fin 26) (product reply : NQ) (events : Fin 2 → NJB_Cuts.Event)
 (calls next : Nat) (after : State) : Prop :=
 offset g.castSucc≤c.val ∧ c.val<offset g.succ ∧
 Canon (terms (pattern c)) ∧ Canon (weights c) ∧ Canon (before g) ∧ Canon product ∧ Canon reply ∧
 calls=2 ∧ (events 0).operation=0 ∧ (events 1).operation=1 ∧
 (events 0).left=terms (pattern c) ∧ (events 0).right=weights c ∧
 (events 1).left=before g ∧ (events 1).right=product ∧ next=c.val+1 ∧
 ∀ i,after i=if i=g then reply else before i
/-- Actual multiplication and addition Results are supplied internally. The
universal cut consumer identifies every mutable post-state cell. -/
theorem discharge (terms : Fin 14 → NQ) (weights : Fin 26 → NQ) (before : State)
 (g : Fin 4) (c : Fin 26) (ht : ∀ i,Canon (terms i)) (hw : ∀ i,Canon (weights i))
 (hb : ∀ i,Canon (before i)) :
 ∃ product reply,FIq_Native.field.QM31.mul (terms (pattern c)) (weights c)=ok product ∧
 FIq_Native.field.QM31.add (before g) product=ok reply ∧ Canon product ∧ Canon reply ∧
 ∀ events calls next after,inner terms weights before g c product reply events calls next after →
 NJB_StateUpdates.mulAdd before g (terms (pattern c)) (weights c)=ok after := by
 obtain ⟨p,cp,hp,_⟩ := NJB_StubLaws.qm_mul (terms (pattern c)) (weights c) (ht _) (hw _)
 obtain ⟨r,cr,hr,_⟩ := NJB_StubLaws.qm_add (before g) p (hb _) hp
 refine ⟨p,r,cp,cr,hp,hr,?_⟩
 intro events calls next after cut
 have frame := cut.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
 have same : after=NJB_StateUpdates.set before g r := by
  funext i
  simpa only [NJB_StateUpdates.set,eq_comm] using frame i
 rw [same]
 simp only [NJB_StateUpdates.mulAdd,NJB_StateUpdates.add,cp,cr,bind_tc_ok]
#print discharge
#print axioms discharge
end AspisR1.NJB_PatternCuts
end
