import NEW_GeometryActual.Funs
import NEW_ShiftLiteral
set_option autoImplicit false
namespace NEW_ShiftAssociation
open Aeneas Aeneas.Std Result

theorem checked_to_wrapping (u : Usize) :
    (u >>> 9#i32 : Result Usize) = ok (Usize.wrapping_shr u 9#u32) := by
  have hbits : 9 < System.Platform.numBits := by decide
  obtain ⟨z,hz,_,bits⟩ := WP.spec_imp_exists
    (Usize.ShiftRight_IScalar_spec u 9#i32 (by decide) (by simpa using hbits))
  rw [hz]
  congr 1
  apply UScalar.eq_of_val_eq
  change z.bv.toNat = (Usize.wrapping_shr u 9#u32).bv.toNat
  apply congrArg BitVec.toNat
  rw [bits,Usize.wrapping_shr_bv_eq]
  change (u.bv >>> 9) = (u.bv >>> (9 % System.Platform.numBits))
  rw [Nat.mod_eq_of_lt hbits]

#print axioms checked_to_wrapping
end NEW_ShiftAssociation
