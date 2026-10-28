import R1Z.BuilderAdmissionRanges
import R1Z.BuilderRecordsAdmission

set_option autoImplicit false
noncomputable section
namespace R1Z.BuilderAdmissionCanonical
open Aeneas Aeneas.Std Result AspisBuilderAdmissionSource R0Z.WriterRefine
open pool_v1.pair_trace BuilderAdmissionStd
attribute [local instance] Classical.propDecidable

theorem canon_iff_list (d : Array U32 8#usize) :
    Canon8 d ↔ ∀ x ∈ d.val, x.val < 2147483647 := by
  constructor
  · intro h x hx
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hx
    have hlt : i < 8 := by simpa only [d.property, UScalar.ofNatCore_val_eq] using hi
    have hv := h i hlt
    simpa only [getElem!_pos d.val i hi, he] using hv
  · intro h i hi
    apply h
    have hlt : i < d.val.length := by simpa only [d.property, UScalar.ofNatCore_val_eq] using hi
    rw [getElem!_pos d.val i hlt]
    exact List.getElem_mem hlt

theorem digest_canonical_spec (d : Array U32 8#usize) :
    ∃ b, digest_canonical d = ok b ∧ (b = true ↔ Canon8 d) := by
  let f := digest_canonical.closure.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool
  let g : U32 → Bool := fun x => decide (x.val < 2147483647)
  have hf : ∀ (c : Unit) (x : U32), f.call_mut c x = ok (g x,c) := by
    intro c x
    change ok (decide (x < aspis_core.field.P),c) = _
    simp only [g, aspis_core.field.P, UScalar.lt_equiv, UScalar.ofNatCore_val_eq]
  obtain ⟨b, after, hr, _, _, _, hb⟩ := iterScan_pure f g hf false
    ⟨Array.to_slice d,0⟩ ()
  refine ⟨b,?_,?_⟩
  · unfold digest_canonical
    simp only [lift, bind_tc_ok, core.slice.Slice.iter]
    change (do let (v,_) ← iterScan f false ⟨Array.to_slice d,0⟩ (); ok v) = ok b
    rw [hr]; rfl
  · have hb' : b = true ↔ ∀ x ∈ d.val, x.val < 2147483647 := by
      simpa [g, Array.to_slice] using hb
    exact hb'.trans (canon_iff_list d).symm

theorem digest_canonical_ok {d : Array U32 8#usize}
    (h : digest_canonical d = ok true) : Canon8 d := by
  obtain ⟨b,hb,hs⟩ := digest_canonical_spec d
  rw [h] at hb
  cases hb
  exact hs.mp rfl

theorem tree_digest_loop_ok (d : Array U32 8#usize) (i : Usize) (hi : i.val ≤ 8)
    (h : pool_v1.pair_tree_profile.digest_is_canonical_loop d i = ok true) :
    ∀ j, i.val ≤ j → j < 8 → (d.val[j]!).val < 2147483647 := by
  generalize he : 8 - i.val = remaining
  induction remaining using Nat.strong_induction_on generalizing i with
  | h remaining ih =>
    rw [pool_v1.pair_tree_profile.digest_is_canonical_loop] at h
    simp only [lift, bind_tc_ok] at h
    have hlen : Slice.len (Array.to_slice d) = 8#usize := by
      apply UScalar.eq_of_val_eq
      simp only [Slice.len_val, Array.length_to_slice]
    rw [hlen] at h
    by_cases hit : i.val < 8
    · rw [if_pos (by simpa [UScalar.lt_equiv] using hit), index_ok d i (by simpa using hit)] at h
      simp only [bind_tc_ok] at h
      by_cases hc : d.val[i.val]! ≥ aspis_core.field.P
      · rw [if_pos hc] at h
        cases h
      · rw [if_neg hc] at h
        have hn := BuilderRecordsArray.next_val i (by omega)
        have tail := ih (8-(Usize.wrapping_add i 1#usize).val) (by omega)
          (Usize.wrapping_add i 1#usize) (by omega) h rfl
        intro j hij hj
        by_cases hji : j = i.val
        · rw [hji]
          have hc' : ¬2147483647 ≤ (d.val[i.val]!).val := by
            simpa only [UScalar.le_equiv, aspis_core.field.P, UScalar.ofNatCore_val_eq] using hc
          exact Nat.lt_of_not_ge hc'
        · exact tail j (by omega) hj
    · intro j hij hj
      omega

theorem tree_digest_ok {d : Array U32 8#usize}
    (h : pool_v1.pair_tree_profile.digest_is_canonical d = ok true) : Canon8 d := by
  intro j hj
  exact tree_digest_loop_ok d 0#usize (by simp) h j (by simp) hj

/-- Both selected-sibling candidates are canonical after successful pair
validation, before interpreting any arithmetic occupancy equation. -/
theorem pair_validate_canonical (p : pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1)
    (h : p.validate = ok (.Ok ())) : Canon8 p.first_commitment ∧ Canon8 p.second_commitment := by
  unfold pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1.validate at h
  obtain ⟨b,hb,h⟩ := BuilderRecordsFields.bind_ok_inv h
  obtain ⟨hb',h⟩ := BuilderAdmissionRanges.error_else h
  have first : Canon8 p.first_commitment := tree_digest_ok (by simpa only [hb'] using hb)
  obtain ⟨b1,hb1,h⟩ := BuilderRecordsFields.bind_ok_inv h
  obtain ⟨hb1',_⟩ := BuilderAdmissionRanges.error_else h
  exact ⟨first,tree_digest_ok (by simpa only [hb1'] using hb1)⟩

theorem digest_canonical_eq (d : Array U32 8#usize) :
    digest_canonical d = ok (decide (Canon8 d)) := by
  obtain ⟨b,hb,hs⟩ := digest_canonical_spec d
  rw [hb]
  by_cases hc : Canon8 d
  · rw [hs.mpr hc]
    simp only [decide_eq_true hc]
  · have hb' : b = false := by cases b <;> simp_all
    rw [hb']
    simp only [decide_eq_false hc]

abbrev Siblings := Array (Array U32 8#usize) 20#usize

theorem siblings_iff_list (d : Siblings) :
    (∀ x ∈ d.val, Canon8 x) ↔ ∀ l, l < 20 → Canon8 d.val[l]! := by
  constructor
  · intro h l hl
    have hlt : l < d.val.length := by simpa only [d.property, UScalar.ofNatCore_val_eq] using hl
    rw [getElem!_pos d.val l hlt]
    exact h _ (List.getElem_mem hlt)
  · intro h x hx
    obtain ⟨l,hl,he⟩ := List.mem_iff_getElem.mp hx
    have hlt : l < 20 := by simpa only [d.property, UScalar.ofNatCore_val_eq] using hl
    simpa only [getElem!_pos d.val l hl, he] using h l hlt

theorem siblings_scan (d : Siblings) :
    ∃ b after,
      core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any
        validate_common.closure.Insts.CoreOpsFunctionFnMutTupleSharedArrayM318Bool
        ⟨Array.to_slice d,0⟩ () = ok (b,after) ∧
      (b = false ↔ ∀ l, l < 20 → Canon8 d.val[l]!) := by
  let f := validate_common.closure.Insts.CoreOpsFunctionFnMutTupleSharedArrayM318Bool
  let g : Array U32 8#usize → Bool := fun x => !(decide (Canon8 x))
  have hf : ∀ (c : Unit) (x : Array U32 8#usize), f.call_mut c x = ok (g x,c) := by
    intro c x
    change (do let b ← digest_canonical x; ok (decide (b ≠ true),c)) = _
    rw [digest_canonical_eq]
    simp only [bind_tc_ok]
    cases hc : decide (Canon8 x) <;> simp [g,hc]
  obtain ⟨b,after,hr,_,_,_,hb⟩ := iterScan_pure f g hf true ⟨Array.to_slice d,0⟩ ()
  refine ⟨b,after,hr,?_⟩
  have hb' : b = false ↔ ∀ x ∈ d.val, Canon8 x := by
    simpa [g, Array.to_slice] using hb
  exact hb'.trans (siblings_iff_list d)

#print axioms canon_iff_list
#print axioms digest_canonical_spec
#print axioms digest_canonical_ok
#print axioms tree_digest_loop_ok
#print axioms tree_digest_ok
#print axioms pair_validate_canonical
#print axioms digest_canonical_eq
#print axioms siblings_iff_list
#print axioms siblings_scan
end R1Z.BuilderAdmissionCanonical
