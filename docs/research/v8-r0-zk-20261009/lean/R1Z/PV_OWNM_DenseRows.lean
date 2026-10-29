import R1Z.PV_OWNL_RowEnumeration
import Mathlib.Algebra.BigOperators.Fin
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OWNM_DenseRows
open scoped BigOperators
open PV_OWNI_DensePrune PV_OWNL_RowEnumeration
variable {K : Type} [Field K]

def fullDense (n : Nat) (p : Fin n → K) (column : Fin (2^n) → K) : K :=
 ∑ r, weight p (tail n r) * column r

theorem high_bit (w t : Nat) (a : Fin (2^w)) (b : Fin (2^t)) (i : Fin w) :
 tail (w+t) (join w t (a,b)) (Fin.castAdd t i) = tail w a i := by
 have h := (PV_OWNJ_Rows.row_decode a.val t b.val b.isLt).1
 have hh := congrArg (fun n : Nat => n.testBit (w-1-i.val)) h
 rw [Nat.testBit_div_two_pow] at hh
 have index : w+t-1-(Fin.castAdd t i).val = w-1-i.val+t := by
  simp only [Fin.coe_castAdd]; omega
 simpa only [tail,join,index] using hh

theorem low_bit (w t : Nat) (a : Fin (2^w)) (b : Fin (2^t)) (i : Fin t) :
 tail (w+t) (join w t (a,b)) (Fin.natAdd w i) = tail t b i := by
 have h := (PV_OWNJ_Rows.row_decode a.val t b.val b.isLt).2
 have hh := congrArg (fun n : Nat => n.testBit (t-1-i.val)) h
 have hi : t-1-i.val<t := by omega
 rw [Nat.testBit_mod_two_pow] at hh
 simp only [show decide (t-1-i.val<t)=true from by simp [hi],Bool.true_and] at hh
 have index : w+t-1-(Fin.natAdd w i).val = t-1-i.val := by
  simp only [Fin.coe_natAdd]; omega
 simpa only [tail,join,index] using hh

/-- Full-coordinate dense weights agree with the integer joined-row weights.
Neither side defines the other through rowEquiv.symm. -/
theorem joined_weight (w t : Nat) (p : Fin (w+t) → K)
 (a : Fin (2^w)) (b : Fin (2^t)) :
 weight p (tail (w+t) (join w t (a,b))) =
 weight (fun i => p (Fin.castAdd t i)) (tail w a) *
 weight (fun i => p (Fin.natAdd w i)) (tail t b) := by
 unfold weight
 rw [Fin.prod_univ_add]
 simp only [high_bit,low_bit]

/-- Ordinary full-row dense evaluation prunes to the scanner suffix, provided
its decoded suffix coordinates are the published Boolean bits. -/
theorem full_dense_sparse (w t : Nat) (p : Fin (w+t) → K)
 (suffix : Fin (2^t)) (column : Fin (2^(w+t)) → K)
 (hs : ∀ i : Fin t, p (Fin.natAdd w i) = if tail t suffix i then 1 else 0) :
 fullDense (w+t) p column =
 ∑ a : Fin (2^w), weight (fun i => p (Fin.castAdd t i)) (tail w a) *
  column (join w t (a,suffix)) := by
 classical
 unfold fullDense
 rw [sum_join]
 apply Finset.sum_congr rfl
 intro a ha
 simp only [joined_weight]
 have hp : (fun i : Fin t => p (Fin.natAdd w i)) =
  (fun i => if tail t suffix i then (1:K) else 0) := funext hs
 rw [hp]
 have hb (b : Fin (2^t)) :
  weight (fun i => if tail t suffix i then (1:K) else 0) (tail t b) =
  if b=suffix then 1 else 0 := by
  rw [boolean_weight]
  by_cases h : b=suffix
  · subst b; simp
  · rw [if_neg (fun he => h (tail_injective t he)),if_neg h]
 simp [hb]

#print axioms high_bit
#print axioms low_bit
#print axioms joined_weight
#print axioms full_dense_sparse
end R1Z.PV_OWNM_DenseRows
