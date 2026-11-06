import NJB_StateUpdates
import NJB_Cuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJL_EndpointCell
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
abbrev State := Fin 103 → NQ
/-- NJL_endpoint_write_cut K012/K011: one native slice assignment at an
arbitrary offset, saved scalar before[observe]/before[index] only. Full frame
is universal in observe; no full103-cell before copy. Native event kind1. -/
def Cut (before after : State) (index : Fin 103) (rhs reply : NQ)
 (event : NJB_Cuts.Event) (calls : Nat) : Prop :=
 calls=1 ∧ event.operation=1 ∧ event.left=before index ∧ event.right=rhs ∧
 ∀ observe,after observe=if observe=index then reply else before observe
/-- Actual complete add Result and SAME arbitrary-window frame, instantiated
without an endpoint or successful-child premise. -/
theorem source (before : State) (index : Fin 103) (rhs : NQ)
 (hb : ∀ i,Canon (before i)) (hr : Canon rhs) :
 ∃ reply after,FIq_Native.field.QM31.add (before index) rhs=ok reply ∧ Canon reply ∧
 NJB_StateUpdates.add before index rhs=ok after ∧ (∀ i,Canon (after i)) ∧
 Cut before after index rhs reply ⟨1,before index,rhs⟩ 1 ∧
 (∀ i,decode (after i)=if i=index then decode (before i)+decode rhs else decode (before i)) := by
 obtain ⟨reply,call,hreply,value⟩ := NJB_StubLaws.qm_add (before index) rhs (hb _) hr
 let after := NJB_StateUpdates.set before index reply
 refine ⟨reply,after,call,hreply,?_,?_,?_,?_⟩
 · simp only [NJB_StateUpdates.add,call,bind_tc_ok];rfl
 · intro i
   dsimp only [after,NJB_StateUpdates.set]
   split <;> first | exact hreply | exact hb i
 · exact ⟨rfl,rfl,rfl,rfl,by intro i;simp only [after,NJB_StateUpdates.set,eq_comm]⟩
 · intro i
   by_cases same : index=i
   · subst i;simp [after,NJB_StateUpdates.set,value]
   · have other : i≠index := Ne.symm same
     simp [after,NJB_StateUpdates.set,same,other]
#print axioms source
end AspisR1.NJL_EndpointCell
end
