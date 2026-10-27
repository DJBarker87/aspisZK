import PoseidonPreparedSum3Source
import FJb_ArrayTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJe_Sum3BridgeBase
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ NC qm cm)
open FIv_PreparedNew (NP prepared)
open FIv_Map (map map_bind map_ok)
open FIv_NativeArithmetic (bind_map)
abbrev Left := Array NP 3#usize
abbrev Right := Array NQ 3#usize
abbrev Sums := Array (Array U64 3#usize) 3#usize
abbrev Components := Array (Array U32 3#usize) 3#usize
abbrev Range := core.ops.range.Range Usize
def left (a : Left) := FJb_ArrayTransport.array prepared a
def right (a : Right) := FJb_ArrayTransport.array qm a
abbrev nativeRow := FIq_Native.field.qm31_from_karatsuba_channel_sums.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call
abbrev oldRow := AspisR1PoseidonPreparedSum3Source.field.qm31_from_karatsuba_channel_sums.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call
/-- Same raw channels and reducer/subtraction order,with only the nominal
CM31 result transported to its retained source owner. -/
theorem row (sums : Array U64 3#usize) : map cm (nativeRow () sums)=oldRow () sums := by
  simp only [nativeRow,oldRow,
    FIq_Native.field.qm31_from_karatsuba_channel_sums.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call,
    AspisR1PoseidonPreparedSum3Source.field.qm31_from_karatsuba_channel_sums.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call,
    cm,map_bind,map_ok,FIv_NativeArithmetic.m31_reduce,FIv_NativeArithmetic.m31_sub]
/-- Actual converter body correspondence;all channel operands are identical. -/
theorem converter (sums : Sums) : map qm (FIq_Native.field.qm31_from_karatsuba_channel_sums sums)=
    AspisR1PoseidonPreparedSum3Source.field.qm31_from_karatsuba_channel_sums sums := by
  simp only [FIq_Native.field.qm31_from_karatsuba_channel_sums,
    AspisR1PoseidonPreparedSum3Source.field.qm31_from_karatsuba_channel_sums,
    ←row,map_bind,map_ok,bind_map,←FIv_NativeCM.by_r,←FIv_NativeCM.add,
    ←FIv_NativeCM.sub,qm]
#print axioms row
#print axioms converter
end AspisR1.FJe_Sum3BridgeBase
end
