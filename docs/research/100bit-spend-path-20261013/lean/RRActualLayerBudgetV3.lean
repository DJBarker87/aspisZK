import RRActualRootLayerBoundV3

open Polynomial
noncomputable section
namespace RRActualSiblingMass
variable {K : Type*} [Field K]
local instance : DecidableEq K := Classical.decEq K

theorem sum_selected_child_root_masses_le_parent_degree
    (g : Nat → K[X]) (p : K[X]) (M : Nat)
    (hp : p ≠ 0) (hzero : g 0 = p) :
    (∑ a ∈ p.roots.toFinset,
      ∑ b ∈ (selectedChildSlice g a p M hp hzero).roots.toFinset,
        (selectedChildSlice g a p M hp hzero).rootMultiplicity b) ≤ p.natDegree := by
  classical
  calc
    (∑ a ∈ p.roots.toFinset,
      ∑ b ∈ (selectedChildSlice g a p M hp hzero).roots.toFinset,
        (selectedChildSlice g a p M hp hzero).rootMultiplicity b) ≤
      ∑ a ∈ p.roots.toFinset,
        (selectedChildSlice g a p M hp hzero).natDegree := by
          apply Finset.sum_le_sum
          intro a ha
          exact RRSiblingMultiplicityMass.sum_rootMultiplicity_over_roots_le_natDegree
            (selectedChildSlice g a p M hp hzero)
    _ ≤ p.natDegree := sum_selected_child_degrees_le_parent_degree g p M hp hzero

/- A layer contains occurrences, so equal values at distinct paths remain distinct.
   Each parent bounds both the next layer's occurrence count and its total mass. -/
def layerMass {α : Type*} (mass : α → Nat) (xs : List α) : Nat :=
  (xs.map mass).sum

def layerStep {α : Type*} (children : α → List α) (xs : List α) : List α :=
  xs.flatMap children

def layerIter {α : Type*} (children : α → List α) : Nat → List α → List α
  | 0, xs => xs
  | n + 1, xs => layerIter children n (layerStep children xs)

theorem layerStep_length_le_mass {α : Type*} (mass : α → Nat)
    (children : α → List α)
    (hchildren : ∀ x, (children x).length ≤ mass x) (xs : List α) :
    (layerStep children xs).length ≤ layerMass mass xs := by
  induction xs with
  | nil => simp [layerStep, layerMass]
  | cons x xs ih =>
      simp only [layerStep, List.flatMap_cons, List.length_append, layerMass,
        List.map_cons, List.sum_cons]
      exact Nat.add_le_add (hchildren x) ih

theorem layerStep_mass_le_mass {α : Type*} (mass : α → Nat)
    (children : α → List α)
    (hchildren : ∀ x, layerMass mass (children x) ≤ mass x) (xs : List α) :
    layerMass mass (layerStep children xs) ≤ layerMass mass xs := by
  induction xs with
  | nil => simp [layerStep, layerMass]
  | cons x xs ih =>
      simp only [layerStep, List.flatMap_cons, List.sum_append, layerMass,
        List.map_append, List.map_cons, List.sum_cons]
      exact Nat.add_le_add (hchildren x) ih

theorem layerIter_mass_le {α : Type*} (mass : α → Nat)
    (children : α → List α)
    (hchildren : ∀ x, layerMass mass (children x) ≤ mass x)
    (n : Nat) (xs : List α) :
    layerMass mass (layerIter children n xs) ≤ layerMass mass xs := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
      exact (ih (layerStep children xs)).trans
        (layerStep_mass_le_mass mass children hchildren xs)

theorem layerIter_succ_length_le_initial_mass {α : Type*} (mass : α → Nat)
    (children : α → List α)
    (hcount : ∀ x, (children x).length ≤ mass x)
    (hmass : ∀ x, layerMass mass (children x) ≤ mass x)
    (n : Nat) (xs : List α) :
    (layerIter children (n + 1) xs).length ≤ layerMass mass xs := by
  induction n generalizing xs with
  | zero =>
      simpa [layerIter] using layerStep_length_le_mass mass children hcount xs
  | succ n ih =>
      change (layerIter children (n + 1) (layerStep children xs)).length ≤ layerMass mass xs
      exact (ih (layerStep children xs)).trans
        (layerStep_mass_le_mass mass children hmass xs)


lemma sum_range_shift (f : Nat → Nat) (D : Nat) :
    (∑ n ∈ Finset.range (D + 1), f n) =
      f 0 + ∑ n ∈ Finset.range D, f (n + 1) := by
  induction D with
  | zero => simp
  | succ D ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      omega

def layerCountTotal {α : Type*} (children : α → List α) (D : Nat) (xs : List α) : Nat :=
  ∑ n ∈ Finset.range (D + 1), (layerIter children n xs).length

theorem layerCountTotal_le_initial_plus_depth_mass {α : Type*}
    (mass : α → Nat) (children : α → List α)
    (hcount : ∀ x, (children x).length ≤ mass x)
    (hmass : ∀ x, layerMass mass (children x) ≤ mass x)
    (D : Nat) (xs : List α) :
    layerCountTotal children D xs ≤ xs.length + D * layerMass mass xs := by
  classical
  rw [layerCountTotal, sum_range_shift]
  simp only [layerIter]
  have htail :
      (∑ n ∈ Finset.range D, (layerIter children (n + 1) xs).length) ≤
        ∑ _n ∈ Finset.range D, layerMass mass xs := by
    apply Finset.sum_le_sum
    intro n hn
    exact layerIter_succ_length_le_initial_mass mass children hcount hmass n xs
  calc
    xs.length + (∑ n ∈ Finset.range D, (layerIter children (n + 1) xs).length) ≤
        xs.length + ∑ _n ∈ Finset.range D, layerMass mass xs := Nat.add_le_add_left htail _
    _ = xs.length + D * layerMass mass xs := by simp [Nat.mul_comm]

#print axioms layerCountTotal_le_initial_plus_depth_mass

#print axioms sum_selected_child_root_masses_le_parent_degree
#print axioms layerStep_length_le_mass
#print axioms layerStep_mass_le_mass
#print axioms layerIter_mass_le
#print axioms layerIter_succ_length_le_initial_mass
end RRActualSiblingMass
