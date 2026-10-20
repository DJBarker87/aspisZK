import AspisFormal.V5FriBitReverse
import R17MinimalReverseBits

set_option autoImplicit false

namespace R17MinimalReverseBitsBridge

/-- The minimal reverseBits copy agrees with the pinned V5 source definition,
by structural recursion only. -/
theorem copied_reverseBits_eq_source (width value : Nat) :
    R17MinimalReverseBits.reverseBits width value =
      AspisV5FriBitReverse.reverseBits width value := by
  induction width generalizing value with
  | zero => rfl
  | succ width ih =>
      change (value % 2) * 2 ^ width +
          R17MinimalReverseBits.reverseBits width (value / 2) =
        (value % 2) * 2 ^ width +
          AspisV5FriBitReverse.reverseBits width (value / 2)
      rw [ih]

/-- Source-owner version of the 9+9 split. -/
theorem reverseBits18_split_source (lo hi : Nat) (hlo : lo < 2 ^ 9)
    (hhi : hi < 2 ^ 9) :
    AspisV5FriBitReverse.reverseBits 18 (2 ^ 9 * hi + lo) =
      AspisV5FriBitReverse.reverseBits 9 lo * 2 ^ 9 +
        AspisV5FriBitReverse.reverseBits 9 hi := by
  rw [← copied_reverseBits_eq_source 18 (2 ^ 9 * hi + lo),
    ← copied_reverseBits_eq_source 9 lo,
    ← copied_reverseBits_eq_source 9 hi]
  exact R17MinimalReverseBits.reverseBits18_split lo hi hlo hhi

end R17MinimalReverseBitsBridge
