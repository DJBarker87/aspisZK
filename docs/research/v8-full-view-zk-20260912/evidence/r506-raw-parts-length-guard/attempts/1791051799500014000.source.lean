import AspisV8R19.R503RawPartsSizeGuard

set_option autoImplicit false

namespace AspisV8R19.R506RawPartsLengthGuard

open Aeneas Aeneas.Std Result

abbrev U64 := Aeneas.UScalar Usize

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
  · have hn : n.val ≤ (18446744073709551615#u64 : U64).val := by
      sorry
    simp [lengthGuard, sizeLimit, hz, hn]
  · have hs : 0 < size.val := by omega
    obtain ⟨limit, hdiv, hval, hnle⟩ :=
      AspisV8R19.R503RawPartsSizeGuard.positive_size_quotient_bound n size hs hbytes
    simp [lengthGuard, sizeLimit, hz, hdiv, hnle]

#print axioms length_guard_true

end AspisV8R19.R506RawPartsLengthGuard
