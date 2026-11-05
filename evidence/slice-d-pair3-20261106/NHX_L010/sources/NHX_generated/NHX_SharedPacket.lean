import NHM_SharedPartialResult
set_option autoImplicit false
namespace NHX_SharedPacket
open Aeneas Aeneas.Std Result ControlFlow AspisR1 LPi_FieldValues
open NHM_SharedPartials

/-- Domain is inherited by every SAME child: immutable message and common
array are threaded without replacement; the side bound follows from state. -/
theorem call_domain (f : Slice U8) (common : Array NQ 16#usize)
 (s : State) (h : NHM_SharedPartialsDomain.Inv s)
 (side : Usize) (next : NHI_RangeProgress.Range)
 (run : core.iter.range.IteratorRange.next core.iter.range.StepUsize s.1=ok (some side,next)) :
 side.val<4 ∧ f=f ∧ common=common :=
 ⟨NHM_SharedPartialsDomain.side_domain s h side next run,rfl,rfl⟩

/-- Complete Result/first-error equality, with the inherited finite induction
and successful-result canonicality; no successful-child premise is used. -/
theorem source (f : Slice U8) (common : Array NQ 16#usize) :
 FIo_Native.weights.shared_partials f common=reference f common :=
 NHM_SharedPartials.cohort f common

/-- One arbitrary selected output cell is changed only on a successful call;
this is the model frame associated with the native arbitrary-prestate window. -/
theorem write_frame (before after : Cells) (side : Usize) (value : NE)
 (run : Array.update before side value=ok after) (j : Nat) (different : j≠side.val) :
 after.val[j]?=before.val[j]? :=
 NHM_ArrayPreserve.frame before after side value run j different

#print axioms call_domain
#print axioms source
#print axioms write_frame
end NHX_SharedPacket
