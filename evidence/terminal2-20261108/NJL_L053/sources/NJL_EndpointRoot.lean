import NJL_EndpointLookup
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJL_EndpointRoot
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
open FIq_Native.pool_v1.pair_forest_copy_terminal
open NJL_EndpointCell (State)
/-- Concrete marker dictionary for the erased Copy argument of the already
CLOSED generic reference. Neither clone operation is called by that body. -/
def copy : core.marker.Copy NQ := ⟨⟨(fun x=>ok x),(fun _ src=>ok src)⟩⟩
theorem selected_value (high : NQ) (weight : U32) (hh : Canon high) (bounded : weight.val≤1) :
 decode (NJL_EndpointWrites.selected high weight)=decode high*(weight.val : K) := by
 obtain ⟨out,call,_,value⟩ := NIH_SelectedBinary.result copy high weight hh bounded
 have eq := Result.ok.inj ((NIH_SelectedBinary.reference copy high weight).symm.trans call)
 change (if weight=1#u32 then high else FIq_Native.field.QM31.ZERO)=out at eq
 rw [show NJL_EndpointWrites.selected high weight=out from eq]
 exact value
def reference (before : State) (s : Selectors) (index : Fin 136) (consumer : Bool)
 (lookup : NJL_EndpointLookup.Cut index consumer) (_tag weight : U32) : Result State :=
 NJL_EndpointWrites.reference before (NJL_EndpointLookup.groupIndex index consumer lookup)
  (NJL_EndpointLookup.patternIndex index consumer lookup) (NJL_EndpointLookup.high s index consumer lookup) weight
/-- Positive genuine-endpoint root. The only cut hypothesis is the reviewed
lookup transcription (ai)(5); all selected/add clauses and the full103-cell
frame are discharged internally. Binary-weight provenance is supplied for
every enclosing caller by NJL_EndpointLookup.caller_weight on its SAME link.
The deployed tag-dot arm ignores every tag value, as does this reference. -/
theorem source (before : State) (s : Selectors) (index : Fin 136) (consumer : Bool)
 (tag weight : U32) (lookup : NJL_EndpointLookup.Cut index consumer)
 (hb : ∀ i,Canon (before i)) (hs : FIw_ArrayValue.canonical s.high) (bounded : weight.val≤1) :
 let g := NJL_EndpointLookup.groupIndex index consumer lookup
 let p := NJL_EndpointLookup.patternIndex index consumer lookup
 let high := NJL_EndpointLookup.high s index consumer lookup
 ∃ first second middle after,
 NDE_Reference12.selected_binary_ref copy high FIq_Native.field.QM31.ZERO weight=ok (NJL_EndpointWrites.selected high weight) ∧
 FIq_Native.field.QM31.add (before (NJL_EndpointIndices.weight g)) (NJL_EndpointWrites.selected high weight)=ok first ∧
 FIq_Native.field.QM31.add (before (NJL_EndpointIndices.pattern p)) high=ok second ∧
 NJL_EndpointCell.Cut before middle (NJL_EndpointIndices.weight g) (NJL_EndpointWrites.selected high weight) first
  ⟨1,before (NJL_EndpointIndices.weight g),NJL_EndpointWrites.selected high weight⟩ 1 ∧
 NJL_EndpointCell.Cut middle after (NJL_EndpointIndices.pattern p) high second
  ⟨1,middle (NJL_EndpointIndices.pattern p),high⟩ 1 ∧
 reference before s index consumer lookup tag weight=ok after ∧ (∀ i,Canon (after i)) ∧
 (∀ i,decode (after i)=if i=NJL_EndpointIndices.weight g then decode (before i)+decode high*(weight.val : K)
  else if i=NJL_EndpointIndices.pattern p then decode (before i)+decode high else decode (before i)) := by
 have hhigh := NJL_EndpointLookup.high_canonical s index consumer lookup hs
 obtain ⟨first,second,middle,after,selected,fcall,scall,mcut,acut,call,ha,value⟩ :=
  NJL_EndpointWrites.source before (NJL_EndpointLookup.groupIndex index consumer lookup)
   (NJL_EndpointLookup.patternIndex index consumer lookup) (NJL_EndpointLookup.high s index consumer lookup) weight hb hhigh
 refine ⟨first,second,middle,after,selected copy,fcall,scall,mcut,acut,call,ha,?_⟩
 intro i
 simpa only [selected_value _ weight hhigh bounded] using value i
#print copy
#print NJL_EndpointLookup.Cut
#print source
#print axioms selected_value
#print axioms source
end AspisR1.NJL_EndpointRoot
end
