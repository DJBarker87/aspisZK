import AspisR1BatchedWeightsValueActualV12
import BatchedWeightsActualReducer
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1BatchedWeightsValueActualV19
open AspisR1BatchedWeightsExtraction
abbrev RawVec := alloc.vec.Vec (Array Std.U64 4#usize)
abbrev Q := aspis_core.field.QM31
abbrev M := aspis_core.field.M31
def qOf (a b c d : M) : Q := { c0 := { a := a, b := b }, c1 := { a := c, b := d } }
private theorem index_usize_ok {α : Type} {n : Usize}
    (a : Array α n) (i : Usize) (hi : i.val < n.val) :
    Array.index_usize a i = .ok (a.val[i.val]'(by simpa [a.property] using hi)) := by
  have hidx : i.val < a.val.length := by simpa [a.property] using hi
  unfold Array.index_usize
  change (match a.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some x => Result.ok x) = Result.ok (a.val[i.val]'hidx)
  rw [List.getElem?_eq_getElem hidx]
theorem value_entry_of_vec_success_canonical
    (raw : RawVec) (terms index : Usize)
    (lane : Array Std.U64 4#usize)
    (hvec : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (Array Std.U64 4#usize)) raw index = .ok lane) :
    ∃ (x0 x1 x2 x3 : Std.U64) (m0 m1 m2 m3 : M),
      Array.index_usize lane 0#usize = .ok x0 ∧
      Array.index_usize lane 1#usize = .ok x1 ∧
      Array.index_usize lane 2#usize = .ok x2 ∧
      Array.index_usize lane 3#usize = .ok x3 ∧
      aspis_core.field.M31.reduce_u64 x0 = .ok m0 ∧
      aspis_core.field.M31.reduce_u64 x1 = .ok m1 ∧
      aspis_core.field.M31.reduce_u64 x2 = .ok m2 ∧
      aspis_core.field.M31.reduce_u64 x3 = .ok m3 ∧
      batched_weights.value_entry raw terms index = .ok (qOf m0 m1 m2 m3) ∧
      m0.val = x0.val % AspisV8R17.RawReducer.P ∧ m0.val < AspisV8R17.RawReducer.P ∧
      m1.val = x1.val % AspisV8R17.RawReducer.P ∧ m1.val < AspisV8R17.RawReducer.P ∧
      m2.val = x2.val % AspisV8R17.RawReducer.P ∧ m2.val < AspisV8R17.RawReducer.P ∧
      m3.val = x3.val % AspisV8R17.RawReducer.P ∧ m3.val < AspisV8R17.RawReducer.P := by
  have hi0 : (0#usize).val < (4#usize).val := by decide
  have hi1 : (1#usize).val < (4#usize).val := by decide
  have hi2 : (2#usize).val < (4#usize).val := by decide
  have hi3 : (3#usize).val < (4#usize).val := by decide
  let x0 : Std.U64 := lane.val[(0#usize).val]'(by simpa [lane.property] using hi0)
  let x1 : Std.U64 := lane.val[(1#usize).val]'(by simpa [lane.property] using hi1)
  let x2 : Std.U64 := lane.val[(2#usize).val]'(by simpa [lane.property] using hi2)
  let x3 : Std.U64 := lane.val[(3#usize).val]'(by simpa [lane.property] using hi3)
  have h0 : Array.index_usize lane 0#usize = .ok x0 := by simpa [x0] using index_usize_ok lane 0#usize hi0
  have h1 : Array.index_usize lane 1#usize = .ok x1 := by simpa [x1] using index_usize_ok lane 1#usize hi1
  have h2 : Array.index_usize lane 2#usize = .ok x2 := by simpa [x2] using index_usize_ok lane 2#usize hi2
  have h3 : Array.index_usize lane 3#usize = .ok x3 := by simpa [x3] using index_usize_ok lane 3#usize hi3
  obtain ⟨m0, r0, hm0, hc0⟩ := AspisR1.BatchedWeightsActualReducer.generated_wrapper_mod x0
  obtain ⟨m1, r1, hm1, hc1⟩ := AspisR1.BatchedWeightsActualReducer.generated_wrapper_mod x1
  obtain ⟨m2, r2, hm2, hc2⟩ := AspisR1.BatchedWeightsActualReducer.generated_wrapper_mod x2
  obtain ⟨m3, r3, hm3, hc3⟩ := AspisR1.BatchedWeightsActualReducer.generated_wrapper_mod x3
  have hout := AspisR1BatchedWeightsValueActualV12.value_entry_four_reads
      raw terms index lane x0 x1 x2 x3 m0 m1 m2 m3 hvec h0 h1 h2 h3 r0 r1 r2 r3
  exact ⟨x0, x1, x2, x3, m0, m1, m2, m3,
    h0, h1, h2, h3, r0, r1, r2, r3, hout, hm0, hc0, hm1, hc1, hm2, hc2, hm3, hc3⟩
#print axioms value_entry_of_vec_success_canonical
end AspisR1BatchedWeightsValueActualV19
