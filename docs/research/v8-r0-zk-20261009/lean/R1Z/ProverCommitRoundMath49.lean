import R1Z.ProverCommitRoundOutput48
import R1Z.BatchedAlgebra
/-! Symbolic sum of the native d/s/t loop and coefficient of the existing
round polynomial. Bounds stay variables; no 4096-term list is evaluated. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitRoundMath49
open Aeneas Aeneas.Std
open ProverCommitCounterList48 ProverCommitRoundOutput48
open ProverCommitRoundLoop48 (Triple)
open scoped BigOperators

variable {K : Type}
section Sums
variable [AddCommMonoid K]

theorem counter_sum (f : Nat → K) (n : Nat) (i : Usize) (bound : i.val+n≤1024) :
    ((counters n i).map (fun j => f j.val)).sum=∑ j : Fin n, f (i.val+j.val) := by
  induction n generalizing i with
  | zero => simp only [counters,List.map_nil,List.sum_nil,Fin.sum_univ_zero]
  | succ n ih =>
    have hv := increment i (by omega)
    rw [counters,List.map_cons,List.sum_cons,ih _ (by rw [hv];omega),Fin.sum_univ_succ]
    simp only [Fin.val_zero,Nat.add_zero,Fin.val_succ,hv]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    omega

theorem flat_sum {A B : Type} (xs : List A) (g : A → List B) (f : B → K) :
    ((xs.flatMap g).map f).sum=(xs.map (fun a => ((g a).map f).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons,List.map_append,List.sum_append,List.map_cons,List.sum_cons,ih]

theorem nested_sum (f : Nat → Nat → Nat → K) (n : Nat) (hn : n≤256) :
    ((indices n).map (fun u => f u.1.val u.2.1.val u.2.2.val)).sum=
      ∑ d : Fin n, ∑ s : Fin 4, ∑ t : Fin 4, f d.val s.val t.val := by
  have ht (d s : Nat) : ((counters 4 0#usize).map (fun t => f d s t.val)).sum=
      ∑ t : Fin 4, f d s t.val := by
    simpa only [show (0#usize).val=0 from rfl,Nat.zero_add] using counter_sum (f d s) 4 0#usize (by decide)
  have hs (d : Nat) : ((counters 4 0#usize).map (fun s =>
      ((counters 4 0#usize).map (fun t => f d s.val t.val)).sum)).sum=
      ∑ s : Fin 4, ∑ t : Fin 4, f d s.val t.val := by
    simp only [ht]
    simpa only [show (0#usize).val=0 from rfl,Nat.zero_add] using
      counter_sum (fun s => ∑ t : Fin 4, f d s t.val) 4 0#usize (by decide)
  simp only [indices,flat_sum,List.map_map,Function.comp_def,hs]
  simpa only [show (0#usize).val=0 from rfl,Nat.zero_add] using
    counter_sum (fun d => ∑ s : Fin 4, ∑ t : Fin 4, f d s.val t.val) n 0#usize (by change 0+n≤1024;omega)

end Sums
section Field
variable [Field K]

def terms (q w : Nat → K) (us : List Triple) (k : Nat) : K :=
  (us.map (fun u => if k=u.2.1.val+ProverCommitRoundStep48.perm u.2.2.val then
    q (4*u.1.val+u.2.1.val)*w (4*u.1.val+u.2.2.val) else 0)).sum

theorem perm_value (t : Fin 4) : ProverCommitRoundStep48.perm t.val=(4-t.val)%4 := by
  fin_cases t <;> rfl

theorem terms_sum (q w : Nat → K) (n : Nat) (hn : n≤256) (k : Nat) :
    terms q w (indices n) k=∑ d : Fin n, ∑ s : Fin 4, ∑ t : Fin 4,
      if k=s.val+(4-t.val)%4 then q (4*d.val+s.val)*w (4*d.val+t.val) else 0 := by
  rw [terms,nested_sum (fun d s t => if k=s+ProverCommitRoundStep48.perm t then q (4*d+s)*w (4*d+t) else 0) n hn]
  simp only [perm_value]

theorem model_coeff (q w : Nat → K) (n k : Nat) :
    (AspisR1.RoundPairing.roundPolynomial (n:=n) (fun j => q j.val) (fun j => w j.val)).coeff k=
      (4 : K)⁻¹*(∑ d : Fin n, ∑ s : Fin 4, ∑ t : Fin 4,
        if k=s.val+(4-t.val)%4 then q (4*d.val+s.val)*w (4*d.val+t.val) else 0) := by
  simp only [AspisR1.RoundPairing.roundPolynomial,Polynomial.finsetSum_coeff,Polynomial.coeff_monomial,
    AspisR1.RoundPairing.quarter,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro t ht
  change (if s.val+(4-t.val)%4=k then (4 : K)⁻¹*q (4*d.val+s.val)*w (4*d.val+t.val) else 0)=_
  by_cases h : k=s.val+(4-t.val)%4
  · rw [if_pos h.symm,if_pos h];ring
  · rw [if_neg (Ne.symm h),if_neg h,mul_zero]

end Field

#print axioms counter_sum
#print axioms flat_sum
#print axioms nested_sum
#print axioms perm_value
#print axioms terms_sum
#print axioms model_coeff
end R1Z.ProverCommitRoundMath49
