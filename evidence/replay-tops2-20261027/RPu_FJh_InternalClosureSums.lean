import RPu_FJh_InternalClosureCallEquations
import RPu_FJh_Base

/-! Bind scalar internal-linear arithmetic to actual captured-array source
callbacks. Both callbacks return their unchanged capture. -/
set_option autoImplicit false
namespace AspisR1.FJh_InternalClosureSums
open Aeneas Aeneas.Std Result WP
open FIq_Native
open AspisR1.FJh_Base (cell)
open AspisR1.FJh_InternalWordOps (wide wide_value)
open AspisR1.ExtractedMaskReducerOps AspisV8R17.RawReducer
abbrev Raw4 := Array U64 4#usize
abbrev Words4 := Array U32 4#usize

def RawBound (a : Raw4) (bound : Nat) : Prop := ∀ j : Fin 4, (cell a j).val < bound
def CanonicalWords (a : Words4) : Prop := ∀ j : Fin 4, (cell a j).val < P

theorem full_sum_call (part : Raw4) (old : Words4) (limb : Usize) (hi : limb.val < 4)
    (hp : RawBound part (15*P)) (ho : CanonicalWords old) :
    ∃ out : U64,
      state_only_poseidon.internal_linear_lazy.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
        (part,old) limb = .ok (out,(part,old)) ∧
      out.val = (cell part (⟨limb.val,hi⟩ : Fin 4)).val +
        (cell old (⟨limb.val,hi⟩ : Fin 4)).val ∧ out.val < 16*P := by
  let index : Fin 4 := ⟨limb.val,hi⟩
  let p := cell part index
  let w := cell old index
  have hb : limb.val < (4#usize).val := by simpa using hi
  have hreadP : Array.index_usize part limb = .ok p := by
    simpa only [p,cell,index] using AspisR1.ExtractedMaskHornerStep.array_index_usize_ok part limb hb
  have hreadW : Array.index_usize old limb = .ok w := by
    simpa only [w,cell,index] using AspisR1.ExtractedMaskHornerStep.array_index_usize_ok old limb hb
  have hpLocal : p.val < 15*P := hp index
  have hwLocal : w.val < P := ho index
  have hsum : p.val+w.val < 16*P := by omega
  have hlimit : 16*P < 2^64 := by norm_num [P]
  have hsum64 : p.val + (wide w).val < 2^64 := by rw [wide_value]; omega
  obtain ⟨out,hadd,hvalue⟩ := add_success p (wide w) hsum64
  rw [wide_value] at hvalue
  refine ⟨out,?_,hvalue,by rw [hvalue]; exact hsum⟩
  rw [AspisR1.FJh_InternalClosureCallEquations.full_call_eq]
  simp only [hreadP,hreadW,hadd,bind_tc_ok]

theorem zero_sum_call (part : Raw4) (old : Words4) (limb : Usize) (hi : limb.val < 4)
    (hp : RawBound part (16*P)) (ho : CanonicalWords old) :
    ∃ out : U64,
      state_only_poseidon.internal_linear_lazy.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
        (part,old) limb = .ok (out,(part,old)) ∧
      out.val = (cell part (⟨limb.val,hi⟩ : Fin 4)).val + P -
        (cell old (⟨limb.val,hi⟩ : Fin 4)).val ∧ out.val < 17*P := by
  let index : Fin 4 := ⟨limb.val,hi⟩
  let p := cell part index
  let w := cell old index
  have hb : limb.val < (4#usize).val := by simpa using hi
  have hreadP : Array.index_usize part limb = .ok p := by
    simpa only [p,cell,index] using AspisR1.ExtractedMaskHornerStep.array_index_usize_ok part limb hb
  have hreadW : Array.index_usize old limb = .ok w := by
    simpa only [w,cell,index] using AspisR1.ExtractedMaskHornerStep.array_index_usize_ok old limb hb
  obtain ⟨out,hzero,hvalue,hbound⟩ := AspisR1.FJh_InternalWordOps.zeroSubtract_success
    p w (hp index) (ho index)
  refine ⟨out,?_,hvalue,hbound⟩
  have hpair : (do
      let value ← AspisR1.FJh_InternalWordOps.zeroSubtract p w
      Result.ok (value,(part,old))) = .ok (out,(part,old)) := by
    rw [hzero]
    rfl
  simp only [AspisR1.FJh_InternalWordOps.zeroSubtract,bind_assoc_eq] at hpair
  rw [AspisR1.FJh_InternalClosureCallEquations.zero_call_eq]
  simp only [hreadP,hreadW,bind_tc_ok]
  exact hpair

#print axioms full_sum_call
#print axioms zero_sum_call
end AspisR1.FJh_InternalClosureSums
