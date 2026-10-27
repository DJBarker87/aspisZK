import RPv_FJh_InternalWordOps

/-! Small source equations keep captured tuple reduction and primitive
operation notation separate from arithmetic witnesses and array models. -/
set_option autoImplicit false
namespace AspisR1.FJh_InternalClosureCallEquations
open Aeneas Aeneas.Std Result
open FIq_Native
open AspisR1.FJh_InternalWordOps (wide)
abbrev Raw4 := Array U64 4#usize
abbrev Words4 := Array U32 4#usize

theorem full_call_eq (part : Raw4) (old : Words4) (limb : Usize) :
    state_only_poseidon.internal_linear_lazy.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
      (part,old) limb = (do
        let p ← Array.index_usize part limb
        let w ← Array.index_usize old limb
        let value ← UScalar.add p (wide w)
        Result.ok (value,(part,old))) := by
  unfold state_only_poseidon.internal_linear_lazy.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
  simp only [lift,bind_tc_ok]
  rfl

theorem zero_call_eq (part : Raw4) (old : Words4) (limb : Usize) :
    state_only_poseidon.internal_linear_lazy.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
      (part,old) limb = (do
        let p ← Array.index_usize part limb
        let added ← UScalar.add p (wide field.P)
        let w ← Array.index_usize old limb
        let value ← UScalar.sub added (wide w)
        Result.ok (value,(part,old))) := by
  unfold state_only_poseidon.internal_linear_lazy.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
  simp only [lift,bind_tc_ok]
  rfl

#print axioms full_call_eq
#print axioms zero_call_eq
end AspisR1.FJh_InternalClosureCallEquations
