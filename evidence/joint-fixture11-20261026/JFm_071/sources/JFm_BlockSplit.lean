import JFw_Blocks
set_option autoImplicit false
namespace AspisR1.JFm_BlockSplit
open Aeneas Aeneas.Std

theorem append (n m : Nat) (a b : List U8) (length : a.length=16*n) :
    JFw_Blocks.blocks (n+m) (a++b)=JFw_Blocks.blocks n a ++ JFw_Blocks.blocks m b := by
  induction n generalizing a with
  | zero =>
    have ha : a=[] := List.length_eq_zero_iff.mp (by omega)
    subst a
    rfl
  | succ n ih =>
    have enough : 16≤a.length := by omega
    have taken : (a.take 16).length=16 := by rw [List.length_take,Nat.min_eq_left enough]
    have restLength : (a.drop 16).length=16*n := by rw [List.length_drop];omega
    have drop : (a++b).drop 16=a.drop 16++b := by
      rw [List.drop_append,List.length_drop]
      simp only [show 16-a.length=0 by omega,List.drop_zero]
    have take : (a++b).take 16=a.take 16 := by
      rw [List.take_append]
      simp only [show 16-a.length=0 by omega,List.take_zero,List.append_nil]
    simp only [show n+1+m=(n+m)+1 by omega,JFw_Blocks.blocks,take,drop,List.cons_append]
    rw [ih _ restLength]

#print axioms append
end AspisR1.JFm_BlockSplit
