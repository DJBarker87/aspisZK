import R1Z.ProverCommitPublicFields34

/-! Successful-return refinement of the actual extracted helpers. There is no
capacity or allocation-success premise: failure and divergence do not satisfy
the successful-return antecedent. This remains a Lean 4.31 backend theorem. -/
set_option autoImplicit false

open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1PublicSerializer.Success431

open FieldsRefinement431
open pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes

theorem extend_success (out out' : ByteVec) (s : Slice Std.U8)
    (h : alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out s = ok out') :
    out'.val = out.val ++ s.val := by
  by_cases hcap : out.length + s.length ≤ Usize.max
  · obtain ⟨v, hv, hval⟩ := extend_u8 out s hcap
    have heq : v = out' := Result.ok.inj (hv.symm.trans h)
    simpa only [heq] using hval
  · simp only [alloc.vec.Vec.extend_from_slice, dif_neg hcap] at h
    cases h

theorem fields_loop_unroll (it : Iter) (out : ByteVec) :
    fields_loop it out = (do
      let r ← fields_loop.body it out
      match r with
      | .cont (it1, out1) => fields_loop it1 out1
      | .done r => ok r) := by
  conv_lhs => unfold fields_loop; rw [loop]
  cases hb : fields_loop.body it out with
  | fail e => simp only [hb, bind_tc_fail]
  | div => simp only [hb, bind_tc_div]
  | ok r =>
    cases r with
    | done r => simp only [hb, bind_tc_ok]
    | cont s =>
      rcases s with ⟨it1, out1⟩
      simp only [hb, bind_tc_ok]
      rfl

theorem fields_loop_success (it : Iter) (out out' : ByteVec)
    (h : fields_loop it out = ok (.Ok (), out')) :
    canonical (remaining it) ∧
      out'.val = out.val ++ encodeWords (remaining it) := by
  rw [fields_loop_unroll] at h
  by_cases hi : it.i < it.slice.val.length
  · let x : Field := it.slice.val[it.i]'hi
    let next : Iter := { it with i := it.i + 1 }
    have hrem : remaining it = x :: remaining next :=
      List.drop_eq_getElem_cons hi
    have hnext : core.slice.iter.IteratorSliceIter.next it = ok (some x, next) := by
      simp only [core.slice.iter.IteratorSliceIter.next, Slice.len_val, dif_pos hi]
      rfl
    simp only [fields_loop.body, hnext, bind_tc_ok] at h
    change (do
      let r ← (if x >= aspis_core.field.P then ok (done (.Err .Public, out))
       else do
         let out1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out
           (Array.to_slice (core.num.U32.to_le_bytes x))
         ok (cont (next, out1)) :
         Result (ControlFlow (Iter × ByteVec) (Status × ByteVec)))
      match r with
      | cont (it1, out1) => fields_loop it1 out1
      | done r => ok r) = ok (.Ok (), out') at h
    by_cases hbad : x >= aspis_core.field.P
    · simp only [if_pos hbad] at h
      cases h
    · simp only [if_neg hbad] at h
      cases hext : alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out
          (Array.to_slice (core.num.U32.to_le_bytes x)) with
      | fail e =>
          simp only [hext, bind_tc_fail] at h
          cases h
      | div =>
          simp only [hext, bind_tc_div] at h
          cases h
      | ok out1 =>
          simp only [hext, bind_tc_ok] at h
          change fields_loop next out1 = ok (.Ok (), out') at h
          have ih := fields_loop_success next out1 out' h
          have hbytes := extend_success out out1
            (Array.to_slice (core.num.U32.to_le_bytes x)) hext
          change out1.val = out.val ++ wordBytes x at hbytes
          have hx : x.val < 2147483647 := by
            rw [noncanonical_iff] at hbad
            omega
          constructor
          · rw [hrem]
            intro y hy
            rcases List.mem_cons.mp hy with rfl | hy
            · exact hx
            · exact ih.1 y hy
          · rw [hrem, ih.2, hbytes]
            simp only [encodeWords, List.flatMap_cons, List.append_assoc]
  · have hrem : remaining it = [] := List.drop_eq_nil_of_le (Nat.le_of_not_gt hi)
    have hnext : core.slice.iter.IteratorSliceIter.next it = ok (none, it) := by
      simp [core.slice.iter.IteratorSliceIter.next, hi]
    simp only [fields_loop.body, hnext, bind_tc_ok] at h
    have heq : out = out' := congrArg Prod.snd (Result.ok.inj h)
    subst out'
    simp [hrem, canonical, encodeWords]
termination_by (remaining it).length
decreasing_by
  simp only [next, remaining, List.length_drop]
  omega

theorem fields_success (out out' : ByteVec) (values : Slice Field)
    (h : fields out values = ok (.Ok (), out')) :
    canonical values.val ∧ out'.val = out.val ++ encodeWords values.val := by
  change fields_loop (⟨values, 0⟩ : Iter) out = ok (.Ok (), out') at h
  simpa only [remaining, List.drop_zero] using fields_loop_success _ out out' h

#print axioms extend_success
#print axioms fields_loop_unroll
#print axioms fields_loop_success
#print axioms fields_success

end AspisR1PublicSerializer.Success431
