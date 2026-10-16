import ExtractedPreparationSerializerFields
import PublicSerializerSuccess431

/-! Exact full field-loop transport. The recursion is justified by the
actual shared-slice iterator; allocation is neither assumed nor unfolded. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1PublicPreparation.SerializerLoop
open SerializerFields
open pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes

theorem fields_cont_decreases (it : Iter) (out : ByteVec) (state : State)
    (h : fields_loop.body it out = ok (cont state)) :
    state.1.slice.val.length - state.1.i < it.slice.val.length - it.i := by
  by_cases hi : it.i < it.slice.val.length
  · let value : U32 := it.slice.val[it.i]'hi
    let next : Iter := { it with i := it.i + 1 }
    have hnext : core.slice.iter.IteratorSliceIter.next it = ok (some value, next) := by
      simp only [core.slice.iter.IteratorSliceIter.next, Slice.len_val, dif_pos hi]
      rfl
    simp only [fields_loop.body, hnext, bind_tc_ok] at h
    change (if value >= aspis_core.field.P then
        ok (done (core.result.Result.Err aspis_core.state_only_prefix.r0.Error.Public, out))
      else do
        let out1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out
          (Array.to_slice (core.num.U32.to_le_bytes value))
        ok (cont (next, out1))) = ok (cont state) at h
    by_cases hbad : value >= aspis_core.field.P
    · simp only [if_pos hbad] at h
      cases h
    · simp only [if_neg hbad] at h
      cases hext : alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out
          (Array.to_slice (core.num.U32.to_le_bytes value)) with
      | fail e =>
          simp only [hext, bind_tc_fail] at h
          cases h
      | div =>
          simp only [hext, bind_tc_div] at h
          cases h
      | ok out1 =>
          simp only [hext, bind_tc_ok] at h
          have hs : (next, out1) = state := ControlFlow.cont.inj (Result.ok.inj h)
          rw [← hs]
          change it.slice.val.length - (it.i + 1) < it.slice.val.length - it.i
          omega
  · have hnext : core.slice.iter.IteratorSliceIter.next it = ok (none, it) := by
      simp only [core.slice.iter.IteratorSliceIter.next, Slice.len_val, dif_neg hi]
    simp only [fields_loop.body, hnext, bind_tc_ok] at h
    change ok (done (core.result.Result.Ok (), out)) = ok (cont state) at h
    cases h

theorem new_fields_loop_unroll (it : Iter) (out : ByteVec) :
    fields_loop it out = (do
      let step ← fields_loop.body it out
      match step with
      | cont (next, out1) => fields_loop next out1
      | done result => ok result) := by
  conv_lhs => unfold fields_loop; rw [loop]
  cases hb : fields_loop.body it out with
  | fail e => simp only [hb, bind_tc_fail]
  | div => simp only [hb, bind_tc_div]
  | ok step =>
    cases step with
    | done result => simp only [hb, bind_tc_ok]
    | cont state =>
      rcases state with ⟨next, out1⟩
      simp only [hb, bind_tc_ok]
      rfl

/-- All outcomes, including bad-field errors, allocation failure and divergence.
The exact output vector is preserved without a capacity/success premise. -/
theorem fields_loop_eq (it : Iter) (out : ByteVec) :
    AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields_loop it out =
      mapPairOutcome (fields_loop it out) := by
  rw [AspisR1PublicSerializer.Success431.fields_loop_unroll,
    new_fields_loop_unroll, fields_body_eq]
  cases h : fields_loop.body it out with
  | fail e => rfl
  | div => rfl
  | ok step =>
    cases step with
    | done result =>
      rcases result with ⟨status, out1⟩
      rfl
    | cont state =>
      rcases state with ⟨next, out1⟩
      change
        AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields_loop next out1 =
          mapPairOutcome (fields_loop next out1)
      exact fields_loop_eq next out1
termination_by it.slice.val.length - it.i
decreasing_by exact fields_cont_decreases it out (next, out1) h

theorem fields_eq (out : ByteVec) (values : Slice U32) :
    AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields out values =
      mapPairOutcome (fields out values) := by
  change
    AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields_loop ⟨values, 0⟩ out =
      mapPairOutcome (fields_loop ⟨values, 0⟩ out)
  exact fields_loop_eq _ out

#print axioms fields_cont_decreases
#print axioms new_fields_loop_unroll
#print axioms fields_loop_eq
#print axioms fields_eq
end AspisR1PublicPreparation.SerializerLoop
