import NDO_JFv_TX2_OuterMeaning
import RPu_JFv_TX2_FoldResidue
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFv_TX2_SumBlocks
open Aeneas Aeneas.Std

theorem append (i : Fin 12) (slot : Fin 4) (j : Fin 8) (base n m : Nat) :
    JFv_TX2_InnerMeaning.sum i slot j base (n+m)=JFv_TX2_InnerMeaning.sum i slot j base n+
      JFv_TX2_InnerMeaning.sum i slot j (base+n) m := by
  induction m with
  | zero => simp only [Nat.add_zero,JFv_TX2_InnerMeaning.sum]
  | succ m ih =>
    rw [show n+(m+1)=(n+m)+1 by omega,JFv_TX2_InnerMeaning.sum,ih,JFv_TX2_InnerMeaning.sum]
    simp only [Nat.add_assoc]

theorem source (i : Fin 12) (slot : Fin 4) (j : Fin 8) (n : Nat) (hn : n≤7) :
    JFv_TX2_OuterMeaning.sum i slot j n%2147483647=
      JFv_TX2_InnerMeaning.sum i slot j 0 (min (4*n) 26)%2147483647 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have small : n<7 := by omega
    have prior : min (4*n) 26=4*n := by omega
    have span : min (4*(n+1)) 26=4*n+(min (4*n+4) 26-4*n) := by omega
    rw [JFv_TX2_OuterMeaning.sum,Nat.add_mod,ih (by omega),prior,
      JFv_TX2_OuterStepMeaning.batch,JFv_TX2_FoldResidue.source,span,
      append,show 0+4*n=4*n by omega,Nat.add_mod]
    simp only [Nat.mod_mod]
    exact (Nat.add_mod _ _ _).symm
#print axioms append
#print axioms source
end AspisR1.JFv_TX2_SumBlocks
end
