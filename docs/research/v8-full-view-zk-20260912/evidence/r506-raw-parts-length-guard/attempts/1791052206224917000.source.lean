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
  unfold lengthGuard
  by_cases hz : size.val = 0
  · have hn : n.val ≤ U64.max := by scalar_tac
    have hword : (18446744073709551615#u64 : U64).val = U64.max := by scalar_tac
    have hd : decide (n.val ≤ (18446744073709551615#u64 : U64).val) = true := by
      rw [decide_eq_true_eq, hword]
      exact hn
    simp only [sizeLimit, if_pos hz]
    change Aeneas.Std.Result.ok
      (decide (n.val ≤ (18446744073709551615#u64 : U64).val)) =
      Aeneas.Std.Result.ok true
    rw [hd]
  · have hs : 0 < size.val := by omega
    obtain ⟨limit, hdiv, hval, hnle⟩ :=
      AspisV8R19.R503RawPartsSizeGuard.positive_size_quotient_bound n size hs hbytes
    have hd : decide (n.val ≤ limit.val) = true := decide_eq_true_eq.mpr hnle
    simp only [sizeLimit, if_neg hz, hdiv]
    change Aeneas.Std.Result.ok (decide (n.val ≤ limit.val)) =
      Aeneas.Std.Result.ok true
    rw [hd]

theorem length_guard_image (n size : U64) :
    lengthGuard n size = .ok (decide (n.val * size.val ≤ 9223372036854775807)) := by
  by_cases hz : size.val = 0
  · have hb : n.val * size.val ≤ 9223372036854775807 := by simp [hz]
    rw [length_guard_true n size hb, decide_eq_true hb]
  · have hs : 0 < size.val := by omega
    obtain ⟨limit, hdiv, hval⟩ :=
      UScalar.div_spec AspisV8R19.R503RawPartsSizeGuard.maxIsize (y := size) hz
    have hdiv' : UScalar.div AspisV8R19.R503RawPartsSizeGuard.maxIsize size = .ok limit := by
      simpa [HDiv.hDiv] using hdiv
    have hm : AspisV8R19.R503RawPartsSizeGuard.maxIsize.val = 9223372036854775807 := by
      decide
    have heq : (n.val ≤ limit.val) ↔ (n.val * size.val ≤ 9223372036854775807) := by
      rw [hval, hm]
      exact Nat.le_div_iff_mul_le hs
    unfold lengthGuard
    simp only [sizeLimit, if_neg hz, hdiv']
    change Result.ok (decide (n.val ≤ limit.val)) =
      Result.ok (decide (n.val * size.val ≤ 9223372036854775807))
    rw [propext heq]

#print axioms length_guard_image

#print axioms length_guard_true

end AspisV8R19.R506RawPartsLengthGuard
