import NEV_MaskCarriers
set_option autoImplicit false
noncomputable section
namespace NEV_MaskQM
open Aeneas Aeneas.Std Result AspisR1 NEV_MaskCarriers

theorem add (x y : Native) (hx : LPi_FieldValues.canonQ x) (hy : LPi_FieldValues.canonQ y) :
    (do let out ← FIo_Native.aspis_core.field.QM31.add x y;ok (toMask out)) =
      AspisR1SelectedMaskProbe.field.QM31.add (toMask x) (toMask y) := by
  obtain ⟨native,hn,cn,vn⟩ := LPi_TowerValues.qm_add x y hx hy
  obtain ⟨mask,hm,cm,vm⟩ := ExtractedMaskTowerAdd.current_qm_add_mod
    (toMask x) (toMask y) ((canonical x).mp hx) ((canonical y).mp hy)
  have maskValue : ExtractedMaskQM31Mul.wordsQM mask=LPi_FieldValues.addQ (LPi_FieldValues.qw x) (LPi_FieldValues.qw y) := vm
  have same := words_injective (toMask native) mask
    (by simpa only [words] using vn.trans maskValue.symm)
  simp only [hn,hm,bind_tc_ok,same]

theorem multiply (x y : Native) (hx : LPi_FieldValues.canonQ x) (hy : LPi_FieldValues.canonQ y) :
    (do let out ← FIo_Native.aspis_core.field.QM31.mul x y;ok (toMask out)) =
      AspisR1SelectedMaskProbe.field.QM31.mul (toMask x) (toMask y) := by
  obtain ⟨native,hn,cn,vn⟩ := LPi_TowerValues.qm_mul x y hx hy
  obtain ⟨mask,hm,cm,vm⟩ := ExtractedMaskQM31Mul.current_qm_mul_words
    (toMask x) (toMask y) ((canonical x).mp hx) ((canonical y).mp hy)
  have maskValue : ExtractedMaskQM31Mul.wordsQM mask=LPi_FieldValues.mulQ (LPi_FieldValues.qw x) (LPi_FieldValues.qw y) := by
    rw [product_words]
    exact vm
  have same := words_injective (toMask native) mask
    (by simpa only [words] using vn.trans maskValue.symm)
  simp only [hn,hm,bind_tc_ok,same]

/-- Reuse the retained all-word normalization value law; canonicality of this
actual argument makes each already-proved remainder an identity. -/
theorem normalization (q : Native) (hq : LPi_FieldValues.canonQ q) :
    FIo_Native.aspis_core.field.wide_exact.canonical_qm31 q=ok q := by
  obtain ⟨out,run,canonicalOut,value⟩ := NBG_FieldDischarge.canonical_fio q
  have sameWords : LPi_FieldValues.qw out=LPi_FieldValues.qw q := by
    simpa only [NBG_FieldDischarge.modQ,LPi_FieldValues.qw,LPi_FieldValues.cw,
      Nat.mod_eq_of_lt hq.1.1,Nat.mod_eq_of_lt hq.1.2,
      Nat.mod_eq_of_lt hq.2.1,Nat.mod_eq_of_lt hq.2.2] using value
  exact run.trans (congrArg Result.ok (native_injective out q sameWords))
#print axioms add
#print axioms multiply
#print axioms normalization
end NEV_MaskQM
end
