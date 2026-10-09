import Mathlib

/-! Finite uniform tapes, arbitrary output types, and rational total variation.
All finite sums below are symbolic. No concrete tape/state/trace is evaluated. -/
set_option autoImplicit false
namespace R0Z
noncomputable section
open scoped BigOperators

variable {R T U V : Type}

/-- Uniform expectation over a finite tape. Security statements also require
`Nonempty` tapes; there is no conditioning on successful execution. -/
def mean [Fintype R] (f : R → ℚ) : ℚ := (∑ r, f r) / Fintype.card R

def law [Fintype R] (f : R → V) (v : V) : ℚ := by
  classical
  exact mean (fun r => if f r = v then 1 else 0)

def support [Fintype R] (f : R → V) : Finset V := by
  classical
  exact Finset.univ.image f

private theorem law_zero [Fintype R] (f : R → V) (v : V)
    (hv : v ∉ support f) : law f v = 0 := by
  classical
  have hn : ∀ r, f r ≠ v := by
    intro r he
    exact hv (Finset.mem_image.mpr ⟨r, Finset.mem_univ r, he⟩)
  simp only [law, mean, if_neg (hn _), Finset.sum_const_zero, zero_div]

/-- Standard total variation: half the L1 difference on the union of supports.
The output need not be finite (e.g. messages include arbitrary polynomials). -/
def dist [Fintype R] [Fintype T] (f : R → V) (g : T → V) : ℚ := by
  classical
  exact (∑ v ∈ support f ∪ support g, |law f v - law g v|) / 2

def EqualLaws [Fintype R] [Fintype T] (f : R → V) (g : T → V) : Prop :=
  ∀ v, law f v = law g v

theorem dist_nonneg [Fintype R] [Fintype T] (f : R → V) (g : T → V) :
    0 ≤ dist f g := by
  classical
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (by norm_num)

theorem dist_zero_of_equalLaws [Fintype R] [Fintype T]
    (f : R → V) (g : T → V) (h : EqualLaws f g) : dist f g = 0 := by
  classical
  unfold dist
  have hz : ∀ v, |law f v - law g v| = 0 := fun v => by rw [h v, sub_self, abs_zero]
  simp only [hz, Finset.sum_const_zero, zero_div]

private theorem dist_on [Fintype R] [Fintype T]
    (f : R → V) (g : T → V) (s : Finset V)
    (hf : support f ⊆ s) (hg : support g ⊆ s) :
    dist f g = (∑ v ∈ s, |law f v - law g v|) / 2 := by
  classical
  unfold dist
  congr 1
  apply Finset.sum_subset (Finset.union_subset hf hg)
  intro v _ hn
  have hf' : v ∉ support f := fun h => hn (Finset.mem_union_left _ h)
  have hg' : v ∉ support g := fun h => hn (Finset.mem_union_right _ h)
  rw [law_zero f v hf', law_zero g v hg', sub_self, abs_zero]

theorem dist_triangle [Fintype R] [Fintype T] [Fintype U]
    (f : R → V) (g : T → V) (h : U → V) :
    dist f h ≤ dist f g + dist g h := by
  classical
  let s := (support f ∪ support g) ∪ support h
  have hf : support f ⊆ s := fun _ hv =>
    Finset.mem_union_left _ (Finset.mem_union_left _ hv)
  have hg : support g ⊆ s := fun _ hv =>
    Finset.mem_union_left _ (Finset.mem_union_right _ hv)
  have hh : support h ⊆ s := fun _ hv => Finset.mem_union_right _ hv
  rw [dist_on f h s hf hh, dist_on f g s hf hg, dist_on g h s hg hh, ← add_div]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun v _ => abs_sub_le (law f v) (law g v) (law h v))

#print axioms mean
#print axioms law
#print axioms support
#print axioms law_zero
#print axioms dist
#print axioms EqualLaws
#print axioms dist_nonneg
#print axioms dist_zero_of_equalLaws
#print axioms dist_on
#print axioms dist_triangle
end
end R0Z
