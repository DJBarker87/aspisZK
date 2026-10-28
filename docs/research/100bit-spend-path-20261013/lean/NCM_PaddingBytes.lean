import NCM_PaddingCover

set_option autoImplicit false
namespace AspisR1.NCM_PaddingBytes
open Aeneas Aeneas.Std

/-- The physical U8 value representation preserves the zero predicate. -/
theorem all_zero (xs : List U8) :
    (MultiproofConeCanonical.bytesOf xs).all (fun b => b == 0) = xs.all (fun b => b == 0#u8) := by
  induction xs with
  | nil => rfl
  | cons b rest ih =>
    simp only [MultiproofConeCanonical.bytesOf,List.map_cons,List.all_cons]
    have byte : (AspisV8R19.SqueezeOracleBridge.decodeByte b == 0) = (b == 0#u8) := by
      by_cases zero : b = 0#u8
      · subst b;rfl
      · have value : AspisV8R19.SqueezeOracleBridge.decodeByte b ≠ 0 := by
          intro eq
          exact zero (UScalar.eq_of_val_eq (congrArg Fin.val eq))
        simp only [beq_eq_false_iff_ne.mpr value,beq_eq_false_iff_ne.mpr zero]
    rw [byte]
    have tail := ih
    simp only [MultiproofConeCanonical.bytesOf] at tail
    rw [tail]

/-- The mathematical whole-word scan is exactly the physical byte predicate
on its source-derived width, including arbitrary nonzero padding. -/
theorem scan (padding : Slice U8) (words : Nat) (length : padding.val.length = 8*words) :
    MultiproofConePadding.scan words (MultiproofConeCanonical.bytesOf padding.val) =
      padding.val.all (fun b => b == 0#u8) := by
  rw [MultiproofConePadding.scan_all words _ (by simpa only [MultiproofConeCanonical.bytesOf,List.length_map] using length)]
  exact all_zero padding.val

#print axioms all_zero
#print axioms scan
end AspisR1.NCM_PaddingBytes
