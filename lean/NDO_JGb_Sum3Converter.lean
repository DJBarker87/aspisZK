import NDO_JGb_Sum3Channel
set_option autoImplicit false
namespace AspisR1.JGb_Sum3Converter
open Aeneas Aeneas.Std Result
open FIv_Map (map map_bind map_ok)
open FIv_NativeArithmetic (NC qm cm bind_map m31_reduce m31_sub)
open JGb_Sum3Channel (Sums)
theorem row (a : Array U64 3#usize) :
    map cm (FIq_Native.field.qm31_from_karatsuba_channel_sums.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call () a)=
    AspisR1PoseidonPreparedSum3Source.field.qm31_from_karatsuba_channel_sums.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call () a := by
  simp only [FIq_Native.field.qm31_from_karatsuba_channel_sums.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call,
    AspisR1PoseidonPreparedSum3Source.field.qm31_from_karatsuba_channel_sums.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call,
    map_bind,map_ok,cm,m31_reduce,m31_sub]
#print axioms row

theorem mapped (sums : Sums) :
    map qm (FIq_Native.field.qm31_from_karatsuba_channel_sums sums)=
    AspisR1PoseidonPreparedSum3Source.field.qm31_from_karatsuba_channel_sums sums := by
  simp only [FIq_Native.field.qm31_from_karatsuba_channel_sums,
    AspisR1PoseidonPreparedSum3Source.field.qm31_from_karatsuba_channel_sums,
    qm,map_bind,map_ok,← row,← FIv_NativeCM.add,← FIv_NativeCM.sub,← FIv_NativeCM.by_r,bind_map]
#print axioms mapped
end AspisR1.JGb_Sum3Converter
