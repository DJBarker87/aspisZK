import R1Z.PV_RunJoin_TreeValue16

/-! Forward direction of the actual pair-leaf canonicality validator. -/
set_option autoImplicit false
namespace R1Z.PV_RunJoin_DigestCanonical16
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort

theorem tree_loop (d : Array U32 8#usize) (i : Usize) (hi : i.val ≤ 8)
    (hd : Canon8 d) : pool_v1.pair_tree_profile.digest_is_canonical_loop d i = ok true := by
  generalize he : 8-i.val = remaining
  induction remaining using Nat.strong_induction_on generalizing i with
  | h remaining ih =>
    rw [pool_v1.pair_tree_profile.digest_is_canonical_loop]
    simp only [lift,bind_tc_ok]
    have hlen : Slice.len (Array.to_slice d) = 8#usize := by
      apply UScalar.eq_of_val_eq
      simp only [Slice.len_val,Array.length_to_slice]
    rw [hlen]
    by_cases hit : i.val < 8
    · rw [if_pos (by simpa [UScalar.lt_equiv] using hit),index_ok d i (by simpa using hit)]
      simp only [bind_tc_ok]
      have hnot : ¬d.val[i.val]! ≥ aspis_core.field.P := by
        simp only [UScalar.le_equiv,aspis_core.field.P,UScalar.ofNatCore_val_eq]
        exact Nat.not_le.mpr (hd i.val hit)
      rw [if_neg hnot]
      have hn := BuilderRecordsArray.next_val i (by omega)
      exact ih (8-(Usize.wrapping_add i 1#usize).val) (by omega)
        (Usize.wrapping_add i 1#usize) (by omega) rfl
    · rw [if_neg (by simpa [UScalar.lt_equiv] using hit)]

theorem tree_true (d : Array U32 8#usize) (hd : Canon8 d) :
    pool_v1.pair_tree_profile.digest_is_canonical d = ok true :=
  tree_loop d 0#usize (by simp) hd

#print axioms tree_loop
#print axioms tree_true
end R1Z.PV_RunJoin_DigestCanonical16
