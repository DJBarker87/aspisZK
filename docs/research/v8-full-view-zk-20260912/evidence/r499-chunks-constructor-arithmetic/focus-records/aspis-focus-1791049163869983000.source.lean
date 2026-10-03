import AspisV8R19.R489WordArithmetic

set_option autoImplicit false

/-! Generic arithmetic predecessor for chunks-exact construction. This proves
only the remainder/subtraction values and bounds; it makes no claim about
native allocation, split_at_unchecked, or iterator behavior. -/
namespace AspisV8R19.R499ChunksConstructorArithmetic

open Aeneas Aeneas.Std Result WP

theorem remainder_wrapping_sub (n k : Usize) (hk : 0 < k.val) :
    ∃ r f : Usize,
      UScalar.rem n k = .ok r ∧
      UScalar.wrapping_sub n r = f ∧
      r.val = n.val % k.val ∧
      f.val = n.val - n.val % k.val ∧
      f.val ≤ n.val ∧
      f.val + r.val = n.val := by
  have hnonzero : k.val ≠ 0 := by omega
  have hspec := UScalar.rem_spec n hnonzero
  obtain ⟨r, hrun, hvalue⟩ := spec_imp_exists hspec
  have hrem : UScalar.rem n k = .ok r := by
    simpa [HMod.hMod] using hrun
  have hr : r.val = n.val % k.val := by simpa using hvalue
  have hr_le : r.val ≤ n.val := by
    rw [hr]
    exact Nat.mod_le _ _
  let f : Usize := UScalar.wrapping_sub n r
  have hn_size : n.val < UScalar.size .Usize := by
    simpa [Usize.size, Usize.numBits, UScalarTy.Usize_numBits_eq] using n.hBounds
  have hr_size : r.val < UScalar.size .Usize := by omega
  have hf : f.val = n.val - r.val := by
    change (UScalar.wrapping_sub n r).val = n.val - r.val
    rw [UScalar.wrapping_sub_val_eq]
    have he : n.val + (UScalar.size .Usize - r.val) =
        (n.val - r.val) + UScalar.size .Usize := by omega
    rw [he, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod]
    exact Nat.mod_eq_of_lt (by omega)
  have hf_mod : f.val = n.val - n.val % k.val := by rw [hf, hr]
  have hsum : f.val + r.val = n.val := by
    rw [hf]
    exact Nat.sub_add_cancel hr_le
  refine ⟨r, f, hrem, rfl, hr, hf_mod, ?_, hsum⟩
  rw [hf]
  exact Nat.sub_le _ _

#print axioms remainder_wrapping_sub

end AspisV8R19.R499ChunksConstructorArithmetic
