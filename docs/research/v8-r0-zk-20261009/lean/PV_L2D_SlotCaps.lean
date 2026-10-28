import Mathlib.Tactic
set_option autoImplicit false
namespace PV_L2D_SlotCaps

/-- Source `2 * next_parent_count - occupied_count` at each binary level. -/
def missing (n : Nat → Nat) (d : Nat) : Nat :=
  ∑ i ∈ Finset.range d, (2*n (i+1)-n i)

/-- No normalisation of a large recurrence: this telescopes symbolically. -/
theorem telescope (n : Nat → Nat) (d : Nat)
    (branch : ∀ i<d, n i ≤ 2*n (i+1)) :
    missing n d + n 0 = (∑ i ∈ Finset.range d, n (i+1)) + n d := by
  induction d with
  | zero => simp [missing]
  | succ d ih =>
    have ht := ih (fun i hi => branch i (by omega))
    have hb := branch d (by omega)
    simp only [missing,Finset.sum_range_succ] at ht ⊢
    omega
#print axioms telescope

theorem bottom (n : Nat → Nat) (d : Nat)
    (bound : ∀ i<d, n (i+1)≤n 0) :
    (∑ i ∈ Finset.range d, n (i+1)) ≤ d*n 0 := by
  calc
    _ ≤ ∑ _i ∈ Finset.range d, n 0 := by
      apply Finset.sum_le_sum
      intro i hi
      exact bound i (Finset.mem_range.mp hi)
    _ = d*n 0 := by simp
#print axioms bottom

/-- 18-bit C1/C2 domain: at most k occupied nodes per level, and at most
8,4,2,1 at the top four levels. These occupancy premises still need the
strict-order/domain invariant of the native grouping loop. -/
theorem ordinary (n : Nat → Nat) (k : Nat)
    (initial : n 0≤k)
    (branch : ∀ i<18, n i≤2*n (i+1))
    (low : ∀ i<14, n (i+1)≤n 0)
    (top15 : n 15≤8) (top16 : n 16≤4) (top17 : n 17≤2) (top18 : n 18≤1) :
    missing n 18 ≤ 13*k+16 := by
  have ht := telescope n 18 branch
  have hb := bottom n 14 low
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd] at ht hb
  omega
#print axioms ordinary

/-- Folded queries lie in 16 bits. The binary tree still has 18 levels,
so its two extra single-child levels each contribute one sibling. -/
theorem folded (n : Nat → Nat) (k : Nat)
    (initial : n 0≤k)
    (branch : ∀ i<18, n i≤2*n (i+1))
    (low : ∀ i<12, n (i+1)≤n 0)
    (top13 : n 13≤8) (top14 : n 14≤4) (top15 : n 15≤2)
    (top16 : n 16≤1) (top17 : n 17≤1) (top18 : n 18≤1) :
    missing n 18 ≤ 11*k+18 := by
  have ht := telescope n 18 branch
  have hb := bottom n 12 low
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd] at ht hb
  omega
#print axioms folded

theorem exact_caps :
    13*10+16=146 ∧ 13*12+16=172 ∧ 11*10+18=128 ∧ 11*12+18=150 := by decide
#print axioms exact_caps

theorem padding_length {A : Type} (xs : List A) (cap : Nat) (pad : A)
    (h : xs.length≤cap) :
    (xs ++ List.replicate (cap-xs.length) pad).length = cap := by
  simp only [List.length_append,List.length_replicate]
  omega
#print axioms padding_length
end PV_L2D_SlotCaps
