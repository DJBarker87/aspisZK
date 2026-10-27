import R22Stage2LocalBodies
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9FinalSpanSourceBoundsV1
open AspisR1Stage2
/-- Exact textual reuse of the already proved same-view SliceIndexLength
lemma; its parser import is unnecessary for this generic Std theorem. -/
theorem range_index_success_length {α : Type} (s out : Slice α)
    (start finish : Usize)
    (h : core.slice.index.Slice.index
      (core.slice.index.SliceIndexRangeUsizeSlice α) s
      { start := start, «end» := finish } = Result.ok out) :
    (Slice.len out).val = finish.val - start.val := by
  change core.slice.index.SliceIndexRangeUsizeSlice.index
    { start := start, «end» := finish } s = Result.ok out at h
  simp only [core.slice.index.SliceIndexRangeUsizeSlice.index] at h
  split at h
  · rename_i hbound
    injection h with hout
    subst out
    have hb1 : start.val ≤ finish.val := by
      simpa only [UScalar.le_equiv] using hbound.1
    have hb2 : finish.val ≤ s.val.length := by
      simpa only [UScalar.le_equiv, Slice.length] using hbound.2
    simp [Slice.len, Slice.length, List.slice, hb1, hb2]
    omega
  · cases h

private theorem bind_success {A B : Type} (m : Result A) (next : A → Result B) (out : B)
    (h : (do let x ← m; next x)=.ok out) : ∃ x,m=.ok x ∧ next x=.ok out := by
  cases m with
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
  | ok x => exact ⟨x,rfl,h⟩

/-- The exact pinned source constant body supplies stride2048 symbolically;
no earlier offset chain or absolute proof-buffer address is evaluated. -/
theorem source_openings_after_final (final openings : Usize)
    (hf : compact.OFF_FINAL=.ok final) (ho : compact.OFF_OPENINGS=.ok openings) :
    openings.val=final.val+2048 := by
  unfold compact.OFF_OPENINGS at ho
  obtain ⟨stride,hmul,ho⟩ := bind_success _ _ _ ho
  obtain ⟨final1,hf1,ho⟩ := bind_success _ _ _ ho
  have heq : final1=final := Result.ok.inj (hf1.symm.trans hf)
  subst final1
  unfold compact.FINAL_LEN at hmul
  have hm := UScalar.mul_equiv (64#usize) (32#usize)
  have hop : UScalar.mul (64#usize) (32#usize)=(64#usize*32#usize : Result Usize) := rfl
  rw [hop,hmul] at hm
  have hstride : stride.val=2048 := by
    have hv := hm.2.1
    change stride.val=64*32 at hv
    exact hv
  have ha := UScalar.add_equiv final stride
  rw [ho] at ha
  have hv := ha.2.1
  rw [hstride] at hv
  exact hv

/-- SAME successful final proof range has exactly2048 bytes. This statement
uses the two actual source constant successes and the actual range success,
not a quotient or a postulated View provenance. -/
theorem source_final_range_length (proof bytes : Slice U8) (final openings : Usize)
    (hf : compact.OFF_FINAL=.ok final) (ho : compact.OFF_OPENINGS=.ok openings)
    (hr : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      proof {start:=final,«end»:=openings}=.ok bytes) :
    bytes.val.length=2048 ∧ Slice.len bytes=2048#usize := by
  have hdelta := source_openings_after_final final openings hf ho
  have hlen := range_index_success_length proof bytes final openings hr
  have hbytes : bytes.val.length=2048 := by
    rw [Slice.len_val] at hlen
    change bytes.val.length=openings.val-final.val at hlen
    omega
  refine ⟨hbytes,?_⟩
  apply UScalar.eq_of_val_eq
  rw [Slice.len_val]
  exact hbytes

#print axioms range_index_success_length
#print axioms source_openings_after_final
#print axioms source_final_range_length
end AspisR1S9FinalSpanSourceBoundsV1
