import NDO_JHa_DotContext
import NDO_JHa_DotOuterMeaning
import RPu_JFv_TX2_FoldResidue
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHa_DotSumBlocks
open Aeneas Aeneas.Std

theorem append (d : JHa_DotContext.Data) (j : Fin 8) (base n m : Nat) :
    JHa_DotInnerMeaning.sum d j base (n+m)=JHa_DotInnerMeaning.sum d j base n+
      JHa_DotInnerMeaning.sum d j (base+n) m := by
  induction m with
  | zero => simp only [Nat.add_zero,JHa_DotInnerMeaning.sum]
  | succ m ih =>
    rw [show n+(m+1)=(n+m)+1 by omega,JHa_DotInnerMeaning.sum,ih,JHa_DotInnerMeaning.sum]
    simp only [Nat.add_assoc]

theorem source (d : JHa_DotContext.Data) (j : Fin 8) (n : Nat) (hn : n≤7) :
    JHa_DotOuterMeaning.sum d j n%2147483647=
      JHa_DotInnerMeaning.sum d j 0 (min (4*n) 26)%2147483647 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have small : n<7 := by omega
    have prior : min (4*n) 26=4*n := by omega
    have span : min (4*(n+1)) 26=4*n+(min (4*n+4) 26-4*n) := by omega
    rw [JHa_DotOuterMeaning.sum,Nat.add_mod,ih (by omega),prior,
      JHa_DotOuterStepMeaning.batch,JFv_TX2_FoldResidue.source,span,
      append,show 0+4*n=4*n by omega,Nat.add_mod]
    simp only [Nat.mod_mod]
    exact (Nat.add_mod _ _ _).symm
#print axioms append
#print axioms source
end AspisR1.JHa_DotSumBlocks
end
