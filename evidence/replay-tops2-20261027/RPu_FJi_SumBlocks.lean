import RPt_FJi_OuterValue
import RPu_JFv_TX2_FoldResidue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJi_SumBlocks
open Aeneas Aeneas.Std

theorem append (q : Array U8 608#usize) (g : Array FJi_Accumulations.NE 29#usize) (slot : Usize) (j : Nat) (base n m : Nat) :
    FJi_InnerStep.sum q g slot j base (n+m)=FJi_InnerStep.sum q g slot j base n+
      FJi_InnerStep.sum q g slot j (base+n) m := by
  induction m with
  | zero => simp only [Nat.add_zero,FJi_InnerStep.sum]
  | succ m ih =>
    rw [show n+(m+1)=(n+m)+1 by omega,FJi_InnerStep.sum,ih,FJi_InnerStep.sum]
    simp only [Nat.add_assoc]

theorem source (q : Array U8 608#usize) (g : Array FJi_Accumulations.NE 29#usize) (slot : Usize) (j : Nat) (n : Nat) (hn : n ≤ 7) :
    FJi_OuterStep.sum q g slot j n%2147483647=
      FJi_InnerStep.sum q g slot j 0 (min (4*n) 26)%2147483647 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have small : n<7 := by omega
    have prior : min (4*n) 26=4*n := by omega
    have span : min (4*(n+1)) 26=4*n+(min (4*n+4) 26-4*n) := by omega
    rw [FJi_OuterStep.sum,Nat.add_mod,ih (by omega),prior,
      FJi_OuterTerm.batch,JFv_TX2_FoldResidue.source,span,
      append,show 0+4*n=4*n by omega,Nat.add_mod]
    simp only [Nat.mod_mod]
    exact (Nat.add_mod _ _ _).symm
#print axioms append
#print axioms source
end AspisR1.FJi_SumBlocks
end
