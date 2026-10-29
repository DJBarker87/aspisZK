import R1Z.PV_RunJoin_InactiveValue48
import R1Z.Batched
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_InactiveModel48
open Aeneas Aeneas.Std
open ProverCommitWideOps48
open scoped BigOperators

theorem sum (q : Nat → Raw) (n start : Nat) :
    PV_RunJoin_InactiveValue48.total q n start=
      ∑ i : Fin n, value (q (start+i.val))*PV_RunJoin_InactiveIndicator48.mask (start+i.val) := by
  induction n generalizing start with
  | zero => simp only [PV_RunJoin_InactiveValue48.total,Fin.sum_univ_zero]
  | succ n ih =>
    rw [PV_RunJoin_InactiveValue48.total,Fin.sum_univ_succ,ih]
    simp only [Fin.val_zero,Nat.add_zero,Fin.val_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [show start+1+i.val=start+(i.val+1) from by omega]

theorem mask (j : Fin 1024) : PV_RunJoin_InactiveIndicator48.mask j.val=
    AspisR0.Opening.indicator R0P.copyInactiveRows (AspisR1.rowEquiv.symm j) := by
  rw [PV_RunJoin_InactiveIndicator48.mask,dif_pos j.isLt]
  unfold AspisR0.Opening.indicator
  split <;> rfl

theorem complete (q : Nat → Raw) (ch : R0Z.HonestView.Challenges Exact) :
    PV_RunJoin_InactiveValue48.total q 1024 0=
      R1Z.Batched.ell AspisR1.rowEquiv ch 0 (fun i => value (q i.val)) := by
  rw [sum,R1Z.Batched.ell_zero,R1Z.Batched.dotLinear_apply]
  simp only [Nat.zero_add]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mask,mul_comm]
#print axioms sum
#print axioms mask
#print axioms complete
end R1Z.PV_RunJoin_InactiveModel48
