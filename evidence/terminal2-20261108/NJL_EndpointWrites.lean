import NJL_EndpointIndices
import NIH_SelectedBinary
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJL_EndpointWrites
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
open NJL_EndpointCell (State)
def selected (high : NQ) (weight : U32) : NQ := if weight=1#u32 then high else FIq_Native.field.QM31.ZERO
theorem selected_canonical (high : NQ) (weight : U32) (hh : Canon high) : Canon (selected high weight) := by
 unfold selected
 split <;> first | exact hh | exact FIv_NativeValue.zero.1
/-- Instantiate the CLOSED selected-binary child's full emitted reference law
at the SAME raw words. Copy is erased and universally discharged, not a root
operation-dictionary parameter. -/
theorem selected_call (high : NQ) (weight : U32) :
 ∀ copy : core.marker.Copy NQ,NDE_Reference12.selected_binary_ref copy high FIq_Native.field.QM31.ZERO weight=ok (selected high weight) :=
 fun copy=>NIH_SelectedBinary.reference copy high weight
def reference (before : State) (gc : Fin 30) (pc : Fin 43) (high : NQ) (weight : U32) : Result State := do
 let middle ← NJB_StateUpdates.add before (NJL_EndpointIndices.weight gc) (selected high weight)
 NJB_StateUpdates.add middle (NJL_EndpointIndices.pattern pc) high
/-- Both native source writes and the exact103-cell frame. All selected/add
callee clauses are discharged internally; the lookup's typed gc/pc bounds
are exactly its genuine-endpoint native certificate domain. -/
theorem source (before : State) (gc : Fin 30) (pc : Fin 43) (high : NQ) (weight : U32)
 (hb : ∀ i,Canon (before i)) (hh : Canon high) :
 ∃ first second middle after,
 (∀ copy : core.marker.Copy NQ,NDE_Reference12.selected_binary_ref copy high FIq_Native.field.QM31.ZERO weight=ok (selected high weight)) ∧
 FIq_Native.field.QM31.add (before (NJL_EndpointIndices.weight gc)) (selected high weight)=ok first ∧
 FIq_Native.field.QM31.add (before (NJL_EndpointIndices.pattern pc)) high=ok second ∧
 NJL_EndpointCell.Cut before middle (NJL_EndpointIndices.weight gc) (selected high weight) first
  ⟨1,before (NJL_EndpointIndices.weight gc),selected high weight⟩ 1 ∧
 NJL_EndpointCell.Cut middle after (NJL_EndpointIndices.pattern pc) high second
  ⟨1,middle (NJL_EndpointIndices.pattern pc),high⟩ 1 ∧
 reference before gc pc high weight=ok after ∧ (∀ i,Canon (after i)) ∧
 (∀ i,decode (after i)=if i=NJL_EndpointIndices.weight gc then decode (before i)+decode (selected high weight)
  else if i=NJL_EndpointIndices.pattern pc then decode (before i)+decode high else decode (before i)) := by
 obtain ⟨first,middle,fcall,_,mcall,hm,mcut,mvalue⟩ := NJL_EndpointCell.source before (NJL_EndpointIndices.weight gc) (selected high weight) hb (selected_canonical high weight hh)
 obtain ⟨second,after,scall,_,acall,ha,acut,avalue⟩ := NJL_EndpointCell.source middle (NJL_EndpointIndices.pattern pc) high hm hh
 have separate := NJL_EndpointIndices.disjoint gc pc
 have middle_pattern : middle (NJL_EndpointIndices.pattern pc)=before (NJL_EndpointIndices.pattern pc) := by
  have frame := mcut.2.2.2.2
  simpa only [if_neg (Ne.symm separate)] using frame (NJL_EndpointIndices.pattern pc)
 refine ⟨first,second,middle,after,selected_call high weight,fcall,?_,mcut,acut,?_,ha,?_⟩
 · simpa only [middle_pattern] using scall
 · simp only [reference,mcall,bind_tc_ok,acall]
 · intro i
   rw [avalue i,mvalue i]
   by_cases hw : i=NJL_EndpointIndices.weight gc
   · have hp : i≠NJL_EndpointIndices.pattern pc := by rw [hw];exact separate
     simp [hw,hp,separate,Ne.symm separate]
   · by_cases hp : i=NJL_EndpointIndices.pattern pc
     · simp [hw,hp,separate,Ne.symm separate]
     · simp [hw,hp]
#print source
#print axioms selected_canonical
#print axioms selected_call
#print axioms source
end AspisR1.NJL_EndpointWrites
end
