import PV_B3P_DependencyClosure557227
import PV_B3P_ArrayHelpers559227
import PV_B3P_NthFormattingFinal559227
namespace PV_B3P_ClosureFinal559227
open Aeneas Aeneas.Std core.ops.range PV_B3P_Groups14227
set_option autoImplicit false
/-- Extension at the same source-control scope as the existing nine ports.
This does not assert coverage of the complete lowered native graph. -/
inductive Port where
  | previous (i : PV_B3P_Closure557227.Port557)
  | nth | array_read16 | array_write4 | copy

def Signature (α : Type) : Port → Type
  | .previous i => PV_B3P_Closure557227.Signature557 α i
  | .nth => Range Usize → Usize → Result (Option Usize × Range Usize)
  | .array_read16 => Array α 16#usize → Range Usize → Result (Slice α)
  | .array_write4 => Array α 4#usize → RangeTo Usize → Result (Slice α × (Slice α → Array α 4#usize))
  | .copy => core.marker.Copy α → Slice α → Slice α → Result (Slice α)

def source (α : Type) : (i : Port) → Signature α i
  | .previous i => PV_B3P_Closure557227.source557 α i
  | .nth => PV_B3P_NthSourceFinal559227.source
  | .array_read16 => PV_B3P_ArrayHelpers559227.read_source
  | .array_write4 => PV_B3P_ArrayHelpers559227.write_source
  | .copy => fun _ => PV_B3P_ArrayHelpers559227.copy_source

def model (α : Type) : (i : Port) → Signature α i
  | .previous i => PV_B3P_Closure557227.model557 α i
  | .nth => PV_B3P_Std559Kernel227.core.ops.range.Range.Insts.CoreIterRangeRangeIteratorImpl.spec_nth
      core.iter.range.StepUsize
  | .array_read16 => core.array.Array.index
      (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice α))
  | .array_write4 => core.array.Array.index_mut
      (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeToUsizeSlice α))
  | .copy => core.slice.Slice.copy_from_slice

theorem partial_closure559 (α : Type) :
    PV_B3P_Link_std_dependency_closure14 (Signature α) (source α) (model α) := by
  intro i
  cases i with
  | previous i => exact PV_B3P_Closure557227.partial_closure557 α i
  | nth => exact funext fun r => funext (PV_B3P_NthSourceFinal559227.source_binding r)
  | array_read16 => exact funext fun a => funext (PV_B3P_ArrayHelpers559227.read16_binding a)
  | array_write4 => exact funext fun a => funext (PV_B3P_ArrayHelpers559227.write4_binding a)
  | copy => exact funext fun inst => funext fun dest => funext (PV_B3P_ArrayHelpers559227.copy_binding inst dest)

#print axioms partial_closure559
end PV_B3P_ClosureFinal559227
