import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Fin
set_option autoImplicit false
namespace PV_L2C_PaddingProducer
variable {A : Type} [AddCommGroup A]
/-- Decoded row projection of sample_mask_h1_padding followed by
balance_qm31_copy_inactive. The random cells are arbitrary. -/
def sampled {n : Nat} (active : Fin n → Bool) (d : Fin n) (random : Fin n → A)
    (i : Fin n) : A := if active i || decide (i=d) then 0 else random i

def excludedSum {n : Nat} (active : Fin n → Bool) (d : Fin n) (v : Fin n → A) : A :=
  ∑ i : Fin n, if !active i && decide (i≠d) then v i else 0

def balanced {n : Nat} (active : Fin n → Bool) (d : Fin n) (v : Fin n → A)
    (i : Fin n) : A := if i=d then -excludedSum active d v else v i

def inactiveSum {n : Nat} (active : Fin n → Bool) (v : Fin n → A) : A :=
  ∑ i : Fin n, if active i then 0 else v i

theorem sampled_active {n : Nat} (active : Fin n → Bool) (d : Fin n)
    (random : Fin n → A) (i : Fin n) (hi : active i=true) :
    sampled active d random i=0 := by simp [sampled,hi]
#print axioms sampled_active

theorem balanced_active {n : Nat} (active : Fin n → Bool) (d : Fin n)
    (random : Fin n → A) (hd : active d=false) (i : Fin n) (hi : active i=true) :
    balanced active d (sampled active d random) i=0 := by
  have hid : i≠d := by intro h; subst i; rw [hd] at hi; contradiction
  simp [balanced,hid,sampled_active active d random i hi]
#print axioms balanced_active

theorem balanced_sum {n : Nat} (active : Fin n → Bool) (d : Fin n)
    (v : Fin n → A) (hd : active d=false) :
    inactiveSum active (balanced active d v)=0 := by
  classical
  have hsum : inactiveSum active (balanced active d v) =
      -excludedSum active d v + excludedSum active d v := by
    unfold inactiveSum
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ d)]
    simp only [hd, Bool.false_eq_true, if_false, balanced, if_pos rfl]
    congr 1
    unfold excludedSum
    calc
      _ = ∑ i ∈ Finset.univ.erase d, if !active i && decide (i≠d) then v i else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        have hid : i≠d := (Finset.mem_erase.mp hi).1
        cases ha : active i <;> simp [hid,ha]
      _ = _ := by
        apply Finset.sum_subset (Finset.erase_subset d Finset.univ)
        intro i hi he
        have hid : i=d := by
          by_contra h
          exact he (Finset.mem_erase.mpr ⟨h,hi⟩)
        subst i
        simp
  rw [hsum,neg_add_cancel]
#print axioms balanced_sum
/-- The two rejection predicates are both false for every successfully sampled
and balanced padding. No assumption is made about the random values. -/
theorem padding_guards {n : Nat} (active : Fin n → Bool) (d : Fin n)
    (random : Fin n → A) (hd : active d=false) :
    (∀ i, active i=true → balanced active d (sampled active d random) i=0) ∧
      inactiveSum active (balanced active d (sampled active d random))=0 :=
  ⟨fun i hi => balanced_active active d random hd i hi,
    balanced_sum active d _ hd⟩
#print axioms padding_guards
end PV_L2C_PaddingProducer
