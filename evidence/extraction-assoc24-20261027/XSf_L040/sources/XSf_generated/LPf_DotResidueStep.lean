import LPf_DotPushFour
set_option autoImplicit false
namespace AspisR1.LPf_DotResidueStep
open Aeneas Aeneas.Std

theorem source (sum raw : U64) (n : Nat) (hn : n < 4096)
    (hs : sum.val ≤ n*LPf_DotWordStep.bound) :
    (LPf_DotPushFour.update sum raw).val % 2147483647 =
      (sum.val + raw.val) % 2147483647 := by
  unfold LPf_DotPushFour.update
  rw [(LPf_DotWordStep.value sum raw n hn hs).1,LPf_ReductionWord.fold_value]
  rw [Nat.add_mod,LPe_MersenneReduction.fold_mod]
  exact (Nat.add_mod sum.val raw.val 2147483647).symm

#print axioms source
end AspisR1.LPf_DotResidueStep
