import R0P.MaskValue
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring.Basic
/-! Symbolic sufficient statistics for the optimized selected-mask forms. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitLinearMath50
open scoped BigOperators
variable {K : Type} [Field K]

def sum (p : Nat → K) : Nat → K
 | 0 => 0
 | n+1 => sum p n+p n

def weighted (p : Nat → K) : Nat → K
 | 0 => 0
 | n+1 => weighted p n+(n:K)*p n

def stats (p : Nat → K) : Nat → K → K → K × K
 | 0,s,w => (s,w)
 | n+1,s,w => stats p n (s+p n) (if n=0 then w else w+(s+p n))

theorem stats_value (p : Nat → K) (n : Nat) (s w : K) :
    stats p n s w=(s+sum p n,w+((n-1:Nat):K)*s+weighted p n) := by
  induction n generalizing s w with
  | zero => simp [stats,sum,weighted]
  | succ n ih =>
    rw [stats,ih]
    cases n with
    | zero => simp [sum,weighted]
    | succ n =>
      simp only [Nat.add_sub_cancel,Nat.succ_ne_zero,if_false,sum,weighted,Nat.cast_add,Nat.cast_one]
      apply Prod.ext <;> dsimp <;> ring

theorem sum_fin (p : Nat → K) (n : Nat) : sum p n=∑ i : Fin n, p i.val := by
  induction n with
  | zero => simp [sum]
  | succ n ih => rw [sum,ih,Fin.sum_univ_castSucc];rfl

theorem weighted_fin (p : Nat → K) (n : Nat) : weighted p n=∑ i : Fin n, (i.val:K)*p i.val := by
  induction n with
  | zero => simp [weighted]
  | succ n ih => rw [weighted,ih,Fin.sum_univ_castSucc];rfl

theorem form (p : Nat → K) (family : Nat) :
    (3+17*(family:K))*sum p 10+(22+8*(family:K))*weighted p 10=
      R0P.Mask.maskLinear family (fun i : Fin 10 => p i.val) := by
  rw [sum_fin,weighted_fin,R0P.Mask.maskLinear,Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  ring

#print axioms stats_value
#print axioms sum_fin
#print axioms weighted_fin
#print axioms form
end R1Z.ProverCommitLinearMath50
