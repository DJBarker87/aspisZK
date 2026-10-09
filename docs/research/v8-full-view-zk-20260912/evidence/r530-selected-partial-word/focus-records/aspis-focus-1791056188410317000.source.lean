import AspisV8R19.InverseRuntimeMul
import AspisV8R19.R158WordBounds
import AspisR515SharedGamma.QmCrossRange

set_option autoImplicit false
namespace AspisV8R19.R530SelectedPartialWord
open Aeneas Aeneas.Std
open AspisV8R19.InverseRuntimeMul
open AspisV8R19.R158WordBounds
open AspisV8R17.RawReducer
open AspisV8.QmCross

/-- The selected arithmetic shape `(x & 0x7fff_ffff).wrapping_add(x >> 31)`,
expressed with the existing U64 word primitives. The source LLBC builtin
wrapped-I32 shift correspondence remains a separate open bridge. -/
def partialWord (x : U64) : U64 :=
  U64.wrapping_add (UScalar.and x mask64) (U64.wrapping_shr x 31#u32)

theorem partialWord_value (x : U64) :
    (partialWord x).val = partialFold x.val := by
  have hand : (UScalar.and x mask64).val = x.val &&& P := by
    rw [and_value, mask64_value]
  have hshr : (U64.wrapping_shr x 31#u32).val = x.val >>> 31 :=
    wrapping_shr31_value x
  have hfold : foldBits x.val < 2^64 := by
    have h := first_fold_lt x.val x.bv.isLt
    omega
  unfold partialWord
  rw [U64.wrapping_add_val_eq]
  have hmod : ((UScalar.and x mask64).val +
      (U64.wrapping_shr x 31#u32).val) % 2^64 = foldBits x.val := by
    rw [hand, hshr]
    exact Nat.mod_eq_of_lt hfold
  rw [hmod, foldBits_eq_fold31]
  simp only [fold31, partialFold, AspisV8.QmCross.p]
  norm_num

theorem partialWord_range (x : U64) :
    (partialWord x).val < 5*p+4 := by
  rw [partialWord_value]
  apply raw_partial_range
  simpa only [word] using x.bv.isLt

theorem partialWord_mod (x : U64) :
    (partialWord x).val % p = x.val % p := by
  rw [partialWord_value]
  exact partial_congr x.val

#print axioms partialWord_value
#print axioms partialWord_range
#print axioms partialWord_mod
end AspisV8R19.R530SelectedPartialWord
