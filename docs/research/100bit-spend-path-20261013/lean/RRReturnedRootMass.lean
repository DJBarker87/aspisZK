import CompPolyGeneralFiniteRootSampler
import RRSiblingMultiplicityMassV2

noncomputable section
namespace AspisR1.RRReturnedRootMass
open Polynomial CompPoly
open AspisR1.CompPolyGeneralFiniteRootSampler
variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K] [Fintype K]

/-- Any duplicate-free sound returned root list preserves the scalar
multiplicity potential when each actual child is charged at most its
parent-root multiplicity. Completeness and ordering are not needed here. -/
theorem root_list_mass_le_degree (p : K[X]) (hp : p ≠ 0)
    (roots : List K) (hn : roots.Nodup)
    (hsound : ∀ a ∈ roots, IsRoot p a) (mass : K → Nat)
    (hchild : ∀ a ∈ roots, mass a ≤ p.rootMultiplicity a) :
    (roots.map mass).sum ≤ p.natDegree := by
  letI : DecidableEq K := Classical.decEq K
  have hsubset : roots.toFinset ⊆ p.roots.toFinset := by
    intro a ha
    exact Multiset.mem_toFinset.mpr
      ((Polynomial.mem_roots hp).mpr (hsound a (List.mem_toFinset.mp ha)))
  calc
    _ = ∑ a ∈ roots.toFinset, mass a := (List.sum_toFinset mass hn).symm
    _ ≤ ∑ a ∈ roots.toFinset, p.rootMultiplicity a := by
      apply Finset.sum_le_sum
      intro a ha
      exact hchild a (List.mem_toFinset.mp ha)
    _ ≤ ∑ a ∈ p.roots.toFinset, p.rootMultiplicity a :=
      Finset.sum_le_sum_of_subset hsubset
    _ ≤ p.natDegree := RRSiblingMultiplicityMass.sum_rootMultiplicity_over_roots_le_natDegree p

/-- Instantiates that local budget for the actual finite-tape sampler, so
the caller need not assume a canonical order or enumerate the field. -/
theorem finite_sampler_child_mass_le (p : CPolynomial K) (q t : Nat)
    (hq : q = Fintype.card K) (hp : p.toPoly ≠ 0)
    (H : {i : Nat // i ∈ Finset.range (p.natDegree-1)} → Fin t → K × K)
    (roots : List K) (hs : (runGeneralFromFiniteTape p q t H).1 = some roots)
    (mass : K → Nat)
    (hchild : ∀ a ∈ roots, mass a ≤ p.toPoly.rootMultiplicity a) :
    (roots.map mass).sum ≤ p.toPoly.natDegree := by
  have hc := (general_finite_correct p q t hq hp H).2 roots hs
  exact root_list_mass_le_degree p.toPoly hp roots hc.2.1
    (fun a ha => (hc.1 a).mpr ha) mass hchild

#print axioms root_list_mass_le_degree
#print axioms finite_sampler_child_mass_le
end AspisR1.RRReturnedRootMass
