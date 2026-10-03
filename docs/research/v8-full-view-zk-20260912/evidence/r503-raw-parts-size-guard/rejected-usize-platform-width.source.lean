import AspisV8R19.R489WordArithmetic

set_option autoImplicit false

/-! Arithmetic lemma for the positive-element-size branch of raw-parts
construction. No native pointer, alignment, slice-body, or error-branch
correspondence is claimed. -/
namespace AspisV8R19.R503RawPartsSizeGuard

open Aeneas Aeneas.Std Result

def maxIsize : Usize := Usize.ofNatCore 9223372036854775807 (by
  have hbits : UScalarTy.Usize.numBits = 64 := by
    rw [UScalarTy.Usize_numBits_eq]
    decide
  rw [hbits]
  norm_num)

theorem positive_size_quotient_bound (n size : Usize)
    (hs : 0 < size.val)
    (hbytes : n.val * size.val ≤ 9223372036854775807) :
    ∃ limit : Usize,
      UScalar.div maxIsize size = .ok limit ∧
      limit.val = 9223372036854775807 / size.val ∧
      n.val ≤ limit.val := by
  have hnonzero : size.val ≠ 0 := by omega
  obtain ⟨limit, hdiv, hvalue⟩ :=
    UScalar.div_spec maxIsize (y := size) hnonzero
  have hmax : maxIsize.val = 9223372036854775807 := by
    simp [maxIsize, Usize.ofNatCore_val_eq]
  have hvalue' : limit.val = 9223372036854775807 / size.val := by
    simpa [hmax] using hvalue
  have hnle : n.val ≤ 9223372036854775807 / size.val := by
    apply (Nat.le_div_iff_mul_le hs).2
    simpa [hmax] using hbytes
  exact ⟨limit, hdiv, hvalue', by simpa [hvalue'] using hnle⟩

#print axioms positive_size_quotient_bound

end AspisV8R19.R503RawPartsSizeGuard
