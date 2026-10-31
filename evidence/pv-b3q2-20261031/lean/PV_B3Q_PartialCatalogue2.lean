import PV_B3Q_RangeActual
import PV_B3Q_InclusiveActual
import PV_B3Q_MetadataActual
import PV_B3Q_RangeIndexSource
import PV_B3Q_ForwardPointer
namespace PV_B3Q_PartialCatalogue2
open Aeneas Aeneas.Std PV_B3P_Groups14227 core.ops.range
set_option autoImplicit false
/-- Five source-control/state interpretations with actual pinned model roots.
This deliberately excludes unresolved array drain, StepBy, copy, unchecked
pointer and whole-caller obligations. It is not the full op227 catalogue. -/
inductive Body where | range_next | inclusive_next | metadata | range_read | slice_next

def Signature (α : Type) : Body → Type
 | .range_next => Range Usize → Result (Option Usize × Range Usize)
 | .inclusive_next => RangeInclusive Usize → Result (Option Usize × RangeInclusive Usize)
 | .metadata => Slice α → Usize
 | .range_read => Slice α → Range Usize → Result (Slice α)
 | .slice_next => PV_B3Q_ForwardPointer.Cursor α → Result (Option α × core.slice.iter.Iter α)

def source (α : Type) : (i : Body) → Signature α i
 | .range_next => PV_B3Q_RangeActual.source
 | .inclusive_next => PV_B3Q_InclusiveActual.source
 | .metadata => PV_B3Q_MetadataActual.source_len
 | .range_read => PV_B3Q_RangeIndexSource.source
 | .slice_next => fun c => do
    let (item,next) ← PV_B3Q_ForwardPointer.native_next c
    .ok (item,PV_B3Q_ForwardPointer.view next)

def model (α : Type) : (i : Body) → Signature α i
 | .range_next => core.iter.range.IteratorRange.next core.iter.range.StepUsize
 | .inclusive_next => core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next core.iter.range.StepUsize
 | .metadata => Slice.len
 | .range_read => fun s r => core.slice.index.SliceIndexRangeUsizeSlice.index r s
 | .slice_next => fun c => core.slice.iter.IteratorSliceIter.next (PV_B3Q_ForwardPointer.view c)

theorem partial_dependency_link (α : Type) :
 PV_B3P_Link_std_dependency_closure14 (Signature α) (source α) (model α) := by
 intro i
 cases i with
 | range_next => exact funext PV_B3Q_RangeActual.binding
 | inclusive_next => exact funext PV_B3Q_InclusiveActual.binding
 | metadata => exact funext PV_B3Q_MetadataActual.binding
 | range_read => exact funext (fun s => funext (PV_B3Q_RangeIndexSource.binding s))
 | slice_next => exact funext PV_B3Q_ForwardPointer.next_binding

/-- Closed concrete source/model families satisfy this local conjunction at
once. No arbitrary native callback is postulated or assigned to T. -/
theorem joint_instance (α : Type) :
 ∃ native : (i : Body) → Signature α i,
   native = source α ∧ PV_B3P_Link_std_dependency_closure14 (Signature α) native (model α) :=
 ⟨source α,rfl,partial_dependency_link α⟩
#print axioms partial_dependency_link
#print axioms joint_instance
end PV_B3Q_PartialCatalogue2
