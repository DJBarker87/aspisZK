import RPu_FJh_M31DotSource
import RPu_FJh_RawLimbReassembly

/-! Named source equations for the outer four-input traversal and its final
reassembly. The latter reuses the existing release reducer/reassembly proof. -/
set_option autoImplicit false
namespace AspisR1.FJh_M31DotOuterSource
open Aeneas Aeneas.Std Result
open FIq_Native
open AspisR1.FJh_InternalClosureSums (Raw4)
abbrev Iter := core.iter.adapters.step_by.StepBy (core.ops.range.Range Usize)

def finish (raw : Raw4) : Result field.QM31 := do
  let x0 ← Array.index_usize raw 0#usize
  let a ← field.M31.reduce_u64 x0
  let x1 ← Array.index_usize raw 1#usize
  let b ← field.M31.reduce_u64 x1
  let c0 ← field.CM31.new a b
  let x2 ← Array.index_usize raw 2#usize
  let c ← field.M31.reduce_u64 x2
  let x3 ← Array.index_usize raw 3#usize
  let d ← field.M31.reduce_u64 x3
  let c1 ← field.CM31.new c d
  .ok { c0, c1 }

theorem finish_source_eq (raw : Raw4) :
    finish raw = state_only_poseidon.extension_from_raw_limbs raw := by
  simp only [finish,state_only_poseidon.extension_from_raw_limbs,
    field.M31.reduce_u62,field.M31.reduce_u64,bind_assoc_eq,bind_tc_ok]

theorem source_loop_eq (iter : Iter) (weights : Slice field.QM31)
    (values : Slice U32) (sums : Raw4) :
    field.qm31_m31_dot_loop1 iter weights values sums = (do
      let (o,next) ← core.iter.adapters.step_by.IteratorStepBy.next
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) iter
      match o with
      | none => .ok sums
      | some start =>
        let plus ← UScalar.add start 4#usize
        let last ← core.cmp.min core.cmp.OrdUsize plus (Slice.len weights)
        let raw ← field.qm31_m31_dot_loop1_loop0 { start, «end» := last }
          weights values AspisR1.FJh_InternalAccumulateState.zero
        let sums1 ← field.qm31_m31_dot_loop1_loop1
          { start := 0#usize, «end» := 4#usize } sums raw
        field.qm31_m31_dot_loop1 next weights values sums1) := by
  rw [field.qm31_m31_dot_loop1.eq_def]
  rfl

theorem source_long_eq (weights : Slice field.QM31) (values : Slice U32)
    (heq : Slice.len weights = Slice.len values) (hlong : ¬ Slice.len weights ≤ 4#usize) :
    field.qm31_m31_dot weights values = (do
      let iter ← core.iter.traits.iterator.Iterator.step_by.trait_default
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
        { start := 0#usize, «end» := Slice.len weights } 4#usize
      let sums ← field.qm31_m31_dot_loop1 iter weights values
        AspisR1.FJh_InternalAccumulateState.zero
      finish sums) := by
  have hm : massert (Slice.len weights = Slice.len values) = .ok () := by
    simp only [heq,massert,if_pos]
  rw [field.qm31_m31_dot,hm,bind_tc_ok,if_neg hlong]
  rfl

#print axioms finish_source_eq
#print axioms source_loop_eq
#print axioms source_long_eq
end AspisR1.FJh_M31DotOuterSource
