import AspisV8R19.TwoSwapSourceDomains
import AspisV8R19.TwoSwapDistinctRestriction

/-! The source-domain fixed-root bound after restricting the two OOD
coordinates to be distinct.  This is finite-domain plumbing only: it does
not identify a sampler law and makes no privacy claim. -/
set_option autoImplicit false
namespace AspisR19.TwoSwapSourceDistinct
open MvPolynomial
open AspisV8R15.ExactTowerBase
open AspisR19.TwoSwapSourceDomains
open AspisR19.TwoSwapDistinctRestriction
open AspisR19.TwoSwapFixedRootProbability
noncomputable section

def sourceDistinct : Finset (Fin 36 → QM31Exact) :=
  distinctAdmitted sourceDomain

def sourceIm : CM31Exact := ⟨1, 0⟩

theorem sourceIm_ne_zero : sourceIm ≠ 0 := by
  intro h
  have hre := congrArg (fun z : CM31Exact => z.re) h
  change (1 : M31Exact) = 0 at hre
  exact one_ne_zero hre

def sourceOOD0 : QM31Exact := ⟨⟨0, 0⟩, sourceIm⟩

def sourceOOD1 : QM31Exact := ⟨⟨1, 0⟩, sourceIm⟩

def sourceWitness : Fin 36 → QM31Exact := fun i =>
  if i = (10 : Fin 36) then 1
  else if i = (12 : Fin 36) then sourceOOD0
  else if i = (13 : Fin 36) then sourceOOD1
  else 0

theorem sourceOOD0_mem : sourceOOD0 ∈ secureOODDomain := by
  simpa [sourceOOD0, secureOODDomain] using sourceIm_ne_zero

theorem sourceOOD1_mem : sourceOOD1 ∈ secureOODDomain := by
  simpa [sourceOOD1, secureOODDomain] using sourceIm_ne_zero

theorem sourceOOD_ne : sourceOOD0 ≠ sourceOOD1 := by
  intro h
  have := congrArg (fun z : QM31Exact => z.re.re) h
  norm_num [sourceOOD0, sourceOOD1] at this

theorem sourceWitness_mem : sourceWitness ∈ Fintype.piFinset sourceDomain := by
  classical
  rw [Fintype.mem_piFinset]
  intro i
  fin_cases i <;>
    simp [sourceWitness, sourceDomain, fullQM31Domain,
      nonzeroQM31Domain, secureOODDomain, sourceOOD0, sourceOOD1,
      sourceIm_ne_zero]

theorem sourceDistinct_nonempty : sourceDistinct.Nonempty := by
  refine ⟨sourceWitness, ?_⟩
  simp only [sourceDistinct, distinctAdmitted, Finset.mem_filter,
    sourceWitness_mem, true_and]
  intro h
  exact sourceOOD_ne (by simpa [sourceWitness] using h)

theorem fixed_root_distinct_domains_source
    (t : Fin 22 → QM31Exact) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) :
    ((Finset.filter
        (fun s => eval s (determinantFor t ht noneOne) = 0)
        sourceDistinct).card : ℚ≥0) /
        sourceDistinct.card ≤
      ((819 : ℚ≥0) / sourceMinimum) /
        ((sourceDistinct.card : ℚ≥0) /
          (Fintype.piFinset sourceDomain).card) := by
  exact fixed_root_distinct_domains t ht noneOne sourceDomain sourceMinimum
    (by norm_num [sourceMinimum, P]) sourceDomain_card_minimum
    sourceDistinct_nonempty

#print axioms sourceDistinct_nonempty
#print axioms fixed_root_distinct_domains_source
end
end AspisR19.TwoSwapSourceDistinct
