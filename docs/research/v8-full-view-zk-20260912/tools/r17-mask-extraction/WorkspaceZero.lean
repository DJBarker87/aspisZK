import AspisR17MaskSource.Funs

open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR17MaskSource

private theorem increment_small (j : Usize) (hj : j.val < 1024) :
    (Usize.wrapping_add j 1#usize).val = j.val + 1 := by
  have hs : 1024 < UScalar.size .Usize := by
    cases System.Platform.numBits_eq <;> simp_all [Usize.size, Usize.numBits]
  simp only [Usize.wrapping_add_val_eq]
  have h1 : (1#usize).val = 1 := by simp
  rw [h1, Nat.mod_eq_of_lt (by omega)]

/-- Source loop terminates and clears the remaining suffix, preserving the
already cleared prefix. The array contents need not be canonical field words. -/
theorem workspace_zero_loop
    (weights : Array field.QM31 1024#usize) (j : Usize)
    (hj : j.val ≤ 1024)
    (hprefix : ∀ k, k < j.val → weights.val[k]? = some field.QM31.ZERO) :
    ∃ out, r17_mask_workspace.mask_weights_into_loop1 weights j = ok out ∧
      ∀ k, k < 1024 → out.val[k]? = some field.QM31.ZERO := by
  by_cases hlt : j.val < 1024
  · have hcond : j < r17_structured_g.N := by simpa [r17_structured_g.N] using hlt
    have hb : j.val < weights.length := by simpa [Array.length_eq] using hlt
    obtain ⟨updated, hu, rfl⟩ := WP.spec_imp_exists (Array.update_spec weights j field.QM31.ZERO hb)
    have hinc := increment_small j hlt
    have hp : ∀ k, k < (Usize.wrapping_add j 1#usize).val →
        (weights.set j field.QM31.ZERO).val[k]? = some field.QM31.ZERO := by
      intro k hk
      by_cases he : k = j.val
      · subst k
        simp [Array.set_val_eq, hlt]
      · have hkold : k < j.val := by omega
        simp [Array.set_val_eq, he, hprefix k hkold]
    obtain ⟨out, hout, hzero⟩ := workspace_zero_loop
      (weights.set j field.QM31.ZERO) (Usize.wrapping_add j 1#usize)
      (by omega) hp
    refine ⟨out, ?_, hzero⟩
    unfold r17_mask_workspace.mask_weights_into_loop1
    rw [loop.eq_1]
    simp only [r17_mask_workspace.mask_weights_into_loop1.body, if_pos hcond,
      hu, bind_tc_ok, lift]
    exact hout
  · have hcond : ¬ j < r17_structured_g.N := by simpa [r17_structured_g.N] using hlt
    refine ⟨weights, ?_, ?_⟩
    · unfold r17_mask_workspace.mask_weights_into_loop1
      rw [loop.eq_1]
      simp [r17_mask_workspace.mask_weights_into_loop1.body, hcond]
    · intro k hk
      exact hprefix k (by omega)
termination_by 1024 - j.val
decreasing_by
  have := increment_small j hlt
  omega

theorem workspace_zero_from_start (weights : Array field.QM31 1024#usize) :
    ∃ out, r17_mask_workspace.mask_weights_into_loop1 weights 0#usize = ok out ∧
      ∀ k, k < 1024 → out.val[k]? = some field.QM31.ZERO := by
  apply workspace_zero_loop
  · simp
  · simp

theorem workspace_zero_independent
    (a b : Array field.QM31 1024#usize) :
    r17_mask_workspace.mask_weights_into_loop1 a 0#usize =
      r17_mask_workspace.mask_weights_into_loop1 b 0#usize := by
  obtain ⟨oa, ha, hza⟩ := workspace_zero_from_start a
  obtain ⟨ob, hb, hzb⟩ := workspace_zero_from_start b
  have he : oa = ob := by
    apply Subtype.ext
    apply List.ext_getElem?
    intro k
    by_cases hk : k < 1024
    · rw [hza k hk, hzb k hk]
    · have hla : oa.val.length = 1024 := by simpa using oa.property
      have hlb : ob.val.length = 1024 := by simpa using ob.property
      rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  rw [ha, hb, he]

#print axioms workspace_zero_loop
#print axioms workspace_zero_from_start
#print axioms workspace_zero_independent
end AspisR17MaskSource
