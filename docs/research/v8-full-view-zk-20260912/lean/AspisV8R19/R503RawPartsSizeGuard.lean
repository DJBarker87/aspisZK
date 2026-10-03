import AspisV8R19.R489WordArithmetic

set_option autoImplicit false

/-! Arithmetic lemma for the positive-element-size branch of raw-parts
construction over fixed U64 words. The captured x86_64 target has an 8-byte
pointer, but its interpretation as this fixed-U64 model remains a separate
source-to-ABI bridge. No native pointer, alignment, slice-body, or
error-branch correspondence is claimed. -/
namespace AspisV8R19.R503RawPartsSizeGuard

open Aeneas Aeneas.Std Result

def maxIsize : U64 := 9223372036854775807#u64

theorem positive_size_quotient_bound (n size : U64)
    (hs : 0 < size.val)
    (hbytes : n.val * size.val ≤ 9223372036854775807) :
    ∃ limit : U64,
      UScalar.div maxIsize size = .ok limit ∧
      limit.val = 9223372036854775807 / size.val ∧
      n.val ≤ limit.val := by
  have hnonzero : size.val ≠ 0 := by omega
  obtain ⟨limit, hdiv, hvalue⟩ :=
    UScalar.div_spec maxIsize (y := size) hnonzero
  have hmax : maxIsize.val = 9223372036854775807 := by
    decide
  have hvalue' : limit.val = 9223372036854775807 / size.val := by
    simpa [hmax] using hvalue
  have hnle : n.val ≤ 9223372036854775807 / size.val := by
    apply (Nat.le_div_iff_mul_le hs).2
    simpa [hmax] using hbytes
  exact ⟨limit, hdiv, hvalue', by simpa [hvalue'] using hnle⟩

#print axioms positive_size_quotient_bound

end AspisV8R19.R503RawPartsSizeGuard
