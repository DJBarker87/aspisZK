import R1Z.ProverCommitFoldOutput48
import R1Z.BatchedAlgebra
/-! The owned primal fold's cell formula is the existing R1 primalFold. -/
set_option autoImplicit false
namespace R1Z.ProverCommitPrimalModel49
open ProverCommitWideOps48
open scoped BigOperators

theorem horner_model {K : Type} [Field K] (n : Nat) (q : Nat → K) (a : K) (i : Fin n) :
    q (4*i.val)+a*q (4*i.val+1)+a^2*q (4*i.val+2)+a^3*q (4*i.val+3)=
      AspisR1.RoundPairing.primalFold a (fun j : Fin (4*n) => q j.val) i := by
  simp only [AspisR1.RoundPairing.primalFold,Fin.sum_univ_succ,Fin.sum_univ_zero,
    Fin.val_zero,Fin.val_succ,add_zero]
  change q (4*i.val)+a*q (4*i.val+1)+a^2*q (4*i.val+2)+a^3*q (4*i.val+3)=
    q (4*i.val)*a^0+(q (4*i.val+1)*a^1+(q (4*i.val+2)*a^2+q (4*i.val+3)*a^3))
  ring

attribute [local irreducible] value

theorem cell_model (n : Nat) (q : Nat → Raw) (a : Exact) (i : Fin n) :
    ProverCommitFoldOutput48.mathCell (fun j => value (q j)) a i.val=
      AspisR1.RoundPairing.primalFold a (fun j : Fin (4*n) => value (q j.val)) i := by
  rw [←horner_model n (fun j => value (q j)) a i,ProverCommitFoldOutput48.mathCell]

#print axioms horner_model
#print axioms cell_model
end R1Z.ProverCommitPrimalModel49
