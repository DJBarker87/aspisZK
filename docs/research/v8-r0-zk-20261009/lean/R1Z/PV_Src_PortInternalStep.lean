import R1Z.PV_Src_PortReduce
import R1Z.PV_Src_ScalarReduce
import R1Z.BuilderRecordsPath
import R1Z.BuilderBankRange

/-! Exact one-cell equation for the actual internal linear loop. Arithmetic
keeps the source's wrapping shift/add, then uses the proved scalar reducer.
No large permutation or concrete parent cell is reduced. -/
set_option autoImplicit false
namespace R1Z.PV_Src_PortInternalStep
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort
abbrev State := Array U32 16#usize

def cell (state : State) (full : U64) (index : Usize) : U32 :=
  PV_Src_ScalarReduce.value (U64.wrapping_add full
    (U64.wrapping_shl (UScalar.cast .U64 state.val[index.val]!)
      (UScalar.cast .U32 poseidon2.INTERNAL_SHIFTS.val[index.val-1]!)))

theorem canonical (state : State) (full : U64) (index : Usize) :
    (cell state full index).val < 2147483647 :=
  PV_Src_ScalarReduce.canonical _

theorem step (iter after : core.ops.range.Range Usize)
    (state : State) (full : U64) (index : Usize)
    (lo : 1 ≤ index.val) (hi : index.val < 16)
    (next : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      ok (some index,after)) :
    poseidon2.internal_linear_lazy_loop iter state full =
      poseidon2.internal_linear_lazy_loop after
        (state.set index (cell state full index)) full := by
  rw [poseidon2.internal_linear_lazy_loop,next]
  simp only [bind_tc_ok]
  rw [index_ok state index (by simpa using hi)]
  simp only [lift,bind_tc_ok]
  have sub : (Usize.wrapping_sub index 1#usize).val = index.val-1 :=
    BuilderRecordsPath.sub_val index 1#usize (by simpa using lo)
  rw [index_ok_gen poseidon2.INTERNAL_SHIFTS _ (by rw [sub];simp;omega)]
  simp only [lift,bind_tc_ok]
  rw [PV_Src_PortReduce.source,PV_Src_ScalarReduce.reference_eq]
  simp only [bind_tc_ok]
  rw [BuilderRecordsArray.update_gen _ index _ (by simpa using hi)]
  simp only [bind_tc_ok,cell,sub]

#print axioms canonical
#print axioms step
end R1Z.PV_Src_PortInternalStep
