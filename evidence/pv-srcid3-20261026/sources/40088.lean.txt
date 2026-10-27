import R1Z.PV_Src_PortInternalLoop
import R1Z.PV_Src_PortSumAdapter

/-! Source internal-linear body with only the checked sum and scalar cells
left to evaluate. The fifteen-cell loop is replaced by its symbolic theorem. -/
set_option autoImplicit false
namespace R1Z.PV_Src_PortInternalBody
open Aeneas Aeneas.Std Result
open BuilderForestAdmissionPort PV_Src_PortInternalStep

def body (state : State) : Result State := do
  let s ← core.array.Array.index (core.ops.index.IndexSlice
    (core.slice.index.SliceIndexRangeFromUsizeSlice aspis_core.field.M31))
    state { start := 1#usize }
  let part ← PV_Src_PortSumTrace.fold (s.val.map (UScalar.cast .U64)) 0#u64
  let first ← Array.index_usize state 0#usize
  let full := U64.wrapping_add part (UScalar.cast .U64 first)
  let x := U64.wrapping_sub
    (U64.wrapping_add part (UScalar.cast .U64 aspis_core.field.P))
    (UScalar.cast .U64 first)
  let reduced ← aspis_core.field.M31.reduce_u62 x
  let changed ← Array.update state 0#usize reduced
  ok (PV_Src_PortInternalLoop.steps 15 1#usize changed full)

theorem source (state : State) : poseidon2.internal_linear_lazy state = body state := by
  unfold poseidon2.internal_linear_lazy body
  simp only [core.slice.Slice.iter,BuilderStdModels.iterMap,bind_tc_ok,lift,
    BuilderForestStd.sumDefault,BuilderForestStd.sum64,
    BuilderForestStdPort.U64.Insts.CoreIterTraitsAccumSumU64,
    BuilderForestStdPort.U64.Insts.CoreIterTraitsAccumSumU64.sum]
  simp only [PV_Src_PortSumAdapter.sum,List.drop_zero,PV_Src_PortInternalLoop.full_loop]

#print axioms source
end R1Z.PV_Src_PortInternalBody
