import NJB_SharedReference
import NJB_Cuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJL_SharedCuts
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open NJB_SharedReference (group lanes)
abbrev State := Fin 24 → NQ
/-- NJB_K050/K051 full arbitrary24-cell frame plus EXACT one pack/two-call
log; K048/049 and NJL_K033/034 bind all4 gathered inputs and std callbacks. -/
def Cut (values : Fin 33 → NQ) (selector : NQ) (g : Fin 9) (before after : State)
 (packed product reply : NQ) (inputs : Fin 4 → NQ) (events : Fin 2 → NJB_Cuts.Event)
 (packs packLength calls : Nat) : Prop :=
 packs=1 ∧ packLength=4 ∧ calls=2 ∧ inputs=lanes values g ∧
 events 0=⟨0,selector,packed⟩ ∧ events 1=⟨1,before (group g),product⟩ ∧
 (∀ j,after j=if j=group g then reply else before j)
def Step (values : Fin 33 → NQ) (selector : NQ) (g : Fin 9) (before after : State) : Prop :=
 ∃ packed product reply inputs events,
 NJB_PackLaw.reference (lanes values g)=ok packed ∧
 FIq_Native.field.QM31.mul selector packed=ok product ∧
 FIq_Native.field.QM31.add (before (group g)) product=ok reply ∧
 Canon packed ∧ Canon product ∧ Canon reply ∧
 Cut values selector g before after packed product reply inputs events 1 4 2
/-- Each callee clause is discharged internally on exactly the logged operands;
all four padded lanes and all24 destination cells remain associated. -/
theorem source (values : Fin 33 → NQ) (selector : NQ) (g : Fin 9) (before : State)
 (hv : ∀ i,Canon (values i)) (hc : Canon selector) (hb : ∀ i,Canon (before i)) :
 ∃ after,NJB_SharedReference.step values selector g before=ok after ∧
 Step values selector g before after ∧ (∀ i,Canon (after i)) := by
 obtain ⟨packed,cp,hp,_⟩ := NJB_PackLaw.result (lanes values g) (NJB_SharedReference.lanes_canonical values hv g)
 obtain ⟨product,cm,hm,_⟩ := NJB_StubLaws.qm_mul selector packed hc hp
 obtain ⟨reply,ca,ha,_⟩ := NJB_StubLaws.qm_add (before (group g)) product (hb _) hm
 let after := NJB_StateUpdates.set before (group g) reply
 let events : Fin 2 → NJB_Cuts.Event := ![⟨0,selector,packed⟩,⟨1,before (group g),product⟩]
 refine ⟨after,?_,⟨packed,product,reply,lanes values g,events,cp,cm,ca,hp,hm,ha,?_⟩,?_⟩
 · simp only [NJB_SharedReference.step,NJB_StateUpdates.mulAdd,NJB_StateUpdates.add,cp,cm,ca,bind_tc_ok];rfl
 · refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
   intro j;simp only [after,NJB_StateUpdates.set,eq_comm]
 · intro j
   dsimp only [after,NJB_StateUpdates.set]
   split <;> first | exact ha | exact hb j
#print source
#print axioms source
end AspisR1.NJL_SharedCuts
end
