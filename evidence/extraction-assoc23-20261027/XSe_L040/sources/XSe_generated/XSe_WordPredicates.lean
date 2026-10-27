import XSe_WordValue
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XSe_WordPredicates
open XRn_Join_Bytes

theorem canonical (s : Slice U8) (i : Nat) (bound : i+3<s.val.length) :
 decide (XRn_Join_word ((s.val.drop i).take 4)<2147483647#u32)=
 decide (le32 ((s.val.drop i).take 4)<2147483647) := by
 have h := XSe_WordValue.window s i bound
 congr 1
 apply propext
 change (XRn_Join_word ((s.val.drop i).take 4)).val<2147483647 ↔ _
 rw [h]
theorem zero (s : Slice U8) (i : Nat) (bound : i+3<s.val.length) :
 (XRn_Join_word ((s.val.drop i).take 4)==0#u32)=
 decide (le32 ((s.val.drop i).take 4)=0) := by
 have h := XSe_WordValue.window s i bound
 apply Bool.eq_iff_iff.mpr
 simp only [beq_iff_eq,decide_eq_true_eq]
 constructor
 · intro eq
   have v := congrArg UScalar.val eq
   rw [h] at v
   exact v
 · intro z
   apply UScalar.eq_of_val_eq
   change _=0
   rw [h,z]
#print axioms canonical
#print axioms zero
end XSe_WordPredicates
