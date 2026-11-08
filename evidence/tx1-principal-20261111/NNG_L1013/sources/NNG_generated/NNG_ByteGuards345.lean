import NNG_Compare345
import NNG_ReturnAssociation345
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ByteGuards345
open Aeneas Aeneas.Std NMT_345

theorem unequal (xs ys : List U8) :
 ((xs.map byte) != (ys.map byte))=(!decide (xs=ys)) := by
 apply congrArg Bool.not
 apply Bool.eq_iff_iff.mpr
 simp only [beq_iff_eq,decide_eq_true_eq]
 exact NNG_Compare345.projected xs ys
#print axioms unequal

theorem getD (xs : List U8) (n : Nat) :
 (xs.map byte).getD n 0=byte (xs.getD n 0#u8) := by
 induction xs generalizing n with
 | nil=>rfl
 | cons x xs ih=>
  cases n with
  | zero=>rfl
  | succ n=>exact ih n
#print axioms getD

theorem at (xs : List U8) (n : Nat) (h : n < xs.length) :
 (xs.map byte).getD n 0=byte (xs[n]'h) := by
 rw [getD]
 congr 1
 simp only [List.getD,List.getElem?_eq_getElem h,Option.getD_some]
#print axioms at

theorem tag (b : U8) : (byte b != (2 : UInt8))=(b != 2#u8) := by
 exact congrArg Bool.not (NMT_R2_ByteEquality.byte_equal b 2#u8)
#print axioms tag
end AspisR1.NNG_ByteGuards345
