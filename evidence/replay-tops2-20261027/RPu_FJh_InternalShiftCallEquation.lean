import RPu_FJh_InternalWordOps

set_option autoImplicit false
namespace AspisR1.FJh_InternalShiftCallEquation
open Aeneas Aeneas.Std Result
open FIq_Native
open AspisR1.FJh_InternalWordOps (wide)
abbrev Raw4 := Array U64 4#usize
abbrev Words4 := Array U32 4#usize

theorem source_eq (full : Raw4) (words : Words4) (lane limb : Usize) :
    state_only_poseidon.internal_linear_lazy.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
      (full,words,lane) limb = (do
        let p ← Array.index_usize full limb
        let w ← Array.index_usize words limb
        let offset ← UScalar.sub lane 1#usize
        let shift ← Array.index_usize state_only_poseidon.internal_linear_lazy.SHIFTS offset
        let shifted ← wide w <<< shift
        let value ← UScalar.add p shifted
        Result.ok (value,(full,words,lane))) := by
  unfold state_only_poseidon.internal_linear_lazy.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
  simp only [lift,bind_tc_ok]
  rfl

#print axioms source_eq
end AspisR1.FJh_InternalShiftCallEquation
