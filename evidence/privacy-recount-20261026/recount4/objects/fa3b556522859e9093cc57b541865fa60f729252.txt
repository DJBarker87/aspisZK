import AspisR1PublicSerializer34.Funs

/-! Focused refinement of the actual extracted `public_bytes::fields` helper.
Checked with the retained Aeneas Lean 4.31 backend, separately from R1's 4.32
modules. The vector-capacity premise belongs to that backend's Vec model;
this file does not assert concrete allocator success or a Rust runtime theorem.

Generated Funs SHA256:
81a559d23636ee9ef4fccca97efbb53f82890ef1ab8fd644e06a30be0e199656. -/
set_option autoImplicit false

open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1PublicSerializer.FieldsRefinement431

open pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes

abbrev Field := aspis_core.field.M31
abbrev Iter := core.slice.iter.Iter Field
abbrev ByteVec := alloc.vec.Vec Std.U8
abbrev PublicError := aspis_core.state_only_prefix.r0.Error
abbrev Status := core.result.Result Unit PublicError

def wordBytes (x : Field) : List Std.U8 := (core.num.U32.to_le_bytes x).val

theorem wordBytes_length (x : Field) : (wordBytes x).length = 4 := by
  exact (core.num.U32.to_le_bytes x).property

/-- The bytes are the backend's exact little-endian bit-vector encoding. -/
theorem wordBytes_eq_le (x : Field) :
    wordBytes x = x.bv.toLEBytes.map (@UScalar.mk UScalarTy.U8) := rfl

def encodeWords (xs : List Field) : List Std.U8 := xs.flatMap wordBytes

def canonical (xs : List Field) : Prop :=
  ∀ x ∈ xs, x.val < 2147483647

theorem noncanonical_iff (x : Field) :
    x >= aspis_core.field.P ↔ 2147483647 ≤ x.val := by
  unfold aspis_core.field.P
  rfl

/-- A specification of the returned status and bytes, including the exact
prefix retained when the first noncanonical word is encountered. -/
def specFields : List Field → List Std.U8 → Status × List Std.U8
  | [], out => (.Ok (), out)
  | x :: xs, out =>
      if x >= aspis_core.field.P then (.Err .Public, out)
      else specFields xs (out ++ wordBytes x)

def remaining (it : Iter) : List Field := it.slice.val.drop it.i

theorem extend_u8 (out : ByteVec) (s : Slice Std.U8)
    (hcap : out.length + s.length ≤ Usize.max) :
    ∃ out', alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out s = ok out' ∧
      out'.val = out.val ++ s.val := by
  have hclone : Slice.clone core.clone.CloneU8.clone s = ok s := by
    obtain ⟨s', heq, hs⟩ := WP.spec_imp_exists
      (Slice.clone_spec (s := s) (clone := core.clone.CloneU8.clone)
        (by intro x _; rfl))
    simpa [← hs] using heq
  change Slice.clone (liftFun1 core.clone.impls.CloneU8.clone) s = ok s at hclone
  refine ⟨⟨out.val ++ s.val, by simpa using hcap⟩, ?_, rfl⟩
  simp only [alloc.vec.Vec.extend_from_slice, dif_pos hcap]
  split
  · rename_i s' hs'
    have heq : s' = s := Result.ok.inj (hs'.symm.trans hclone)
    subst s'
    rfl
  · rename_i e he
    have impossible : fail e = ok s := he.symm.trans hclone
    cases impossible
  · rename_i he
    have impossible : (div : Result (Slice Std.U8)) = ok s := he.symm.trans hclone
    cases impossible

theorem extend_word (out : ByteVec) (x : Field)
    (hcap : out.length + 4 ≤ Usize.max) :
    ∃ out', alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out
        (Array.to_slice (core.num.U32.to_le_bytes x)) = ok out' ∧
      out'.val = out.val ++ wordBytes x := by
  apply extend_u8
  change out.length + (wordBytes x).length ≤ Usize.max
  rw [wordBytes_length]
  exact hcap

theorem fields_loop_spec (it0 : Iter) (out0 : ByteVec)
    (hcap0 : out0.length + 4 * (remaining it0).length ≤ Usize.max) :
    WP.spec (fields_loop it0 out0)
      (fun r => (r.1, r.2.val) = specFields (remaining it0) out0.val) := by
  let target := specFields (remaining it0) out0.val
  unfold fields_loop
  refine loop.spec_decr_nat
    (fun s : Iter × ByteVec => (remaining s.1).length)
    (fun s => s.2.length + 4 * (remaining s.1).length ≤ Usize.max ∧
      specFields (remaining s.1) s.2.val = target)
    (fun r : Status × ByteVec => (r.1, r.2.val) = target)
    (fun s : Iter × ByteVec => fields_loop.body s.1 s.2)
    (it0, out0) ?_ ⟨hcap0, rfl⟩
  rintro ⟨it, out⟩ ⟨hcap, htarget⟩
  by_cases hi : it.i < it.slice.val.length
  · let x : Field := it.slice.val[it.i]'hi
    let next : Iter := { it with i := it.i + 1 }
    have hrem : remaining it = x :: remaining next := by
      exact List.drop_eq_getElem_cons hi
    have hnext : core.slice.iter.IteratorSliceIter.next it = ok (some x, next) := by
      simp only [core.slice.iter.IteratorSliceIter.next, Slice.len_val, dif_pos hi]
      rfl
    simp only [fields_loop.body, hnext, bind_tc_ok]
    change WP.spec
      (if x >= aspis_core.field.P then ok (done (.Err .Public, out))
       else do
         let out' ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out
           (Array.to_slice (core.num.U32.to_le_bytes x))
         ok (cont (next, out')) :
         Result (ControlFlow (Iter × ByteVec) (Status × ByteVec))) _
    by_cases hbad : x >= aspis_core.field.P
    · rw [if_pos hbad, WP.spec_ok]
      change (core.result.Result.Err aspis_core.state_only_prefix.r0.Error.Public,
        out.val) = target
      simpa only [hrem, specFields, if_pos hbad] using htarget
    · have hroom : out.length + 4 ≤ Usize.max := by
        rw [hrem] at hcap
        simp only [List.length_cons] at hcap
        omega
      obtain ⟨out', hext, hval⟩ := extend_word out x hroom
      rw [if_neg hbad, hext]
      change (out'.length + 4 * (remaining next).length ≤ Usize.max ∧
        specFields (remaining next) out'.val = target) ∧
        (remaining next).length < (remaining it).length
      have hlen : out'.length = out.length + 4 := by
        simp only [alloc.vec.Vec.length, hval, List.length_append, wordBytes_length]
      have heq : specFields (remaining next) out'.val =
          specFields (remaining it) out.val := by
        rw [hrem]
        simp only [specFields, if_neg hbad, hval]
      refine ⟨⟨?_, heq.trans htarget⟩, ?_⟩
      · rw [hrem] at hcap
        simp only [List.length_cons] at hcap
        rw [hlen]
        omega
      · rw [hrem]
        simp
  · have hrem : remaining it = [] :=
      List.drop_eq_nil_of_le (Nat.le_of_not_gt hi)
    have hnext : core.slice.iter.IteratorSliceIter.next it = ok (none, it) := by
      simp [core.slice.iter.IteratorSliceIter.next, hi]
    simp only [fields_loop.body, hnext, bind_tc_ok]
    change (core.result.Result.Ok (), out.val) = target
    simpa only [hrem, specFields] using htarget

theorem fields_spec (out : ByteVec) (values : Slice Field)
    (hcap : out.length + 4 * values.length ≤ Usize.max) :
    ∃ r, fields out values = ok r ∧
      (r.1, r.2.val) = specFields values.val out.val := by
  have hs := fields_loop_spec (⟨values, 0⟩ : Iter) out
    (by simpa [remaining] using hcap)
  apply WP.spec_imp_exists
  simpa [fields, SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,
    remaining] using hs

theorem specFields_canonical (xs : List Field) (out : List Std.U8)
    (h : canonical xs) :
    specFields xs out = (.Ok (), out ++ encodeWords xs) := by
  induction xs generalizing out with
  | nil => simp [specFields, encodeWords]
  | cons x xs ih =>
      have hx : ¬ x >= aspis_core.field.P := by
        rw [noncanonical_iff]
        have := h x (by simp)
        omega
      have hxs : canonical xs := by
        intro y hy
        exact h y (by simp [hy])
      simp [specFields, hx, ih _ hxs, encodeWords, List.append_assoc]

theorem specFields_first_bad (pre post : List Field) (x : Field)
    (out : List Std.U8) (hpre : canonical pre) (hx : 2147483647 ≤ x.val) :
    specFields (pre ++ x :: post) out = (.Err .Public, out ++ encodeWords pre) := by
  have hbad : x >= aspis_core.field.P := (noncanonical_iff x).2 hx
  induction pre generalizing out with
  | nil => simp [specFields, hbad, encodeWords]
  | cons y ys ih =>
      have hy : ¬ y >= aspis_core.field.P := by
        rw [noncanonical_iff]
        have := hpre y (by simp)
        omega
      have hys : canonical ys := by
        intro z hz
        exact hpre z (by simp [hz])
      simp [specFields, hy, ih _ hys, encodeWords, List.append_assoc]

theorem fields_canonical_append (out : ByteVec) (values : Slice Field)
    (hcanonical : canonical values.val)
    (hcap : out.length + 4 * values.length ≤ Usize.max) :
    ∃ out', fields out values = ok (.Ok (), out') ∧
      out'.val = out.val ++ encodeWords values.val := by
  obtain ⟨⟨status, out'⟩, heq, hspec⟩ := fields_spec out values hcap
  rw [specFields_canonical _ _ hcanonical] at hspec
  have hs := congrArg Prod.fst hspec
  have hb := congrArg Prod.snd hspec
  change status = .Ok () at hs
  subst status
  exact ⟨out', heq, hb⟩

theorem fields_reject_first_bad (out : ByteVec) (values : Slice Field)
    (pre post : List Field) (x : Field)
    (hvalues : values.val = pre ++ x :: post) (hpre : canonical pre)
    (hx : 2147483647 ≤ x.val)
    (hcap : out.length + 4 * values.length ≤ Usize.max) :
    ∃ out', fields out values = ok (.Err .Public, out') ∧
      out'.val = out.val ++ encodeWords pre := by
  obtain ⟨⟨status, out'⟩, heq, hspec⟩ := fields_spec out values hcap
  rw [hvalues, specFields_first_bad _ _ _ _ hpre hx] at hspec
  have hs := congrArg Prod.fst hspec
  have hb := congrArg Prod.snd hspec
  change status = .Err .Public at hs
  subst status
  exact ⟨out', heq, hb⟩

#print axioms wordBytes_length
#print axioms wordBytes_eq_le
#print axioms noncanonical_iff
#print axioms extend_u8
#print axioms extend_word
#print axioms fields_loop_spec
#print axioms fields_spec
#print axioms specFields_canonical
#print axioms specFields_first_bad
#print axioms fields_canonical_append
#print axioms fields_reject_first_bad

end AspisR1PublicSerializer.FieldsRefinement431
