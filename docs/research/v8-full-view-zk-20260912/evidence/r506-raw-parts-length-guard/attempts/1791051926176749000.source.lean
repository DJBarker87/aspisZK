import AspisV8R19.R503RawPartsSizeGuard

set_option autoImplicit false

namespace AspisV8R19.R506RawPartsLengthGuard

open Aeneas Aeneas.Std Result

def sizeLimit (size : U64) : Result U64 :=
  if size.val = 0 then .ok (18446744073709551615#u64)
  else UScalar.div AspisV8R19.R503RawPartsSizeGuard.maxIsize size

def lengthGuard (n size : U64) : Result Bool := do
  let limit ← sizeLimit size
  pure (decide (n.val ≤ limit.val))

theorem length_guard_true (n size : U64)
    (hbytes : n.val * size.val ≤ 9223372036854775807) :
    lengthGuard n size = .ok true := by
  by_cases hz : size.val = 0
  · have hn : n.val ≤ U64.max := by
      have hb : n.val < 18446744073709551616 := by
        simpa [UScalar.max, UScalar.size, UScalarTy.numBits] using n.hBounds
      have hm : U64.max = 18446744073709551615 := by
        norm_num [U64.max, U64.size, U64.numBits]
      omega
    have hword : (18446744073709551615#u64 : U64).val = U64.max := by decide
    have hd : decide (n.val ≤ (18446744073709551615#u64 : U64).val) = true := by
      rw [decide_eq_true_eq, hword]
      exact hn
    simp [lengthGuard, sizeLimit, hz, hd]
  · have hs : 0 < size.val := by omega
    obtain ⟨limit, hdiv, hval, hnle⟩ :=
      AspisV8R19.R503RawPartsSizeGuard.positive_size_quotient_bound n size hs hbytes
    have hd : decide (n.val ≤ limit.val) = true := by
      exact decide_eq_true_eq.mpr hnle
    simp [lengthGuard, sizeLimit, hz, hdiv, hd]

#print axioms length_guard_true

end AspisV8R19.R506RawPartsLengthGuard
