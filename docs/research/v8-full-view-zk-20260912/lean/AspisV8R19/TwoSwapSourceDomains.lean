import AspisV8R19.TwoSwapDomainProbability
import AspisV8R15.ExactTowerChord

/-! Exact finite domains for the source-level two-swap parameter map.

This file only records finite-set cardinalities and the coordinate-wise
minimum needed by `fixed_root_domains`.  It does not identify these domains
with the deployed sampler's law, and it makes no privacy claim. -/
set_option autoImplicit false
namespace AspisR19.TwoSwapSourceDomains
open AspisV8R15.ExactTowerBase
open AspisV8R15.ExactTowerChord
open MvPolynomial
open TwoSwapDomainProbability TwoSwapFixedRootProbability
noncomputable section

local instance cm31Fintype : Fintype CM31Exact :=
  Fintype.ofEquiv (M31Exact × M31Exact)
    (QuadraticAlgebra.equivProd (-1 : M31Exact) 0).symm

local instance qm31Fintype : Fintype QM31Exact :=
  Fintype.ofEquiv (CM31Exact × CM31Exact)
    (QuadraticAlgebra.equivProd qm31R 0).symm

def fullQM31Domain : Finset QM31Exact := Finset.univ

def nonzeroQM31Domain : Finset QM31Exact :=
  (Finset.univ : Finset QM31Exact).filter (fun z => z ≠ 0)

def secureOODDomain : Finset QM31Exact :=
  (Finset.univ : Finset QM31Exact).filter (fun z => z.im ≠ 0)

theorem fullQM31Domain_card : fullQM31Domain.card = P ^ 4 := by
  simp [fullQM31Domain, qm31_card]

theorem nonzeroQM31Domain_card : nonzeroQM31Domain.card = P ^ 4 - 1 := by
  calc
    nonzeroQM31Domain.card = Fintype.card {z : QM31Exact // z ≠ 0} := by
      exact (Fintype.card_subtype (fun z : QM31Exact => z ≠ 0)).symm
    _ = Fintype.card QM31Exact - 1 := Set.card_ne_eq (0 : QM31Exact)
    _ = P ^ 4 - 1 := congrArg (fun n => n - 1) qm31_card

def imZeroEquiv : {z : QM31Exact // z.im = 0} ≃ CM31Exact where
  toFun z := z.1.re
  invFun x := ⟨algebraMap CM31Exact QM31Exact x, by simp⟩
  left_inv z := by
    apply Subtype.ext
    ext <;> simp [QuadraticAlgebra.algebraMap_eq, z.2]
  right_inv x := by simp

theorem imZero_card : Fintype.card {z : QM31Exact // z.im = 0} = P ^ 2 := by
  rw [Fintype.card_congr imZeroEquiv, cm31_card]

def secureOODEquiv : {z : QM31Exact // z.im ≠ 0} ≃
    CM31Exact × {z : CM31Exact // z ≠ 0} where
  toFun z := (z.1.re,⟨z.1.im,z.2⟩)
  invFun z := ⟨⟨z.1,z.2.1⟩,z.2.2⟩
  left_inv z := by cases z; rfl
  right_inv z := by cases z; rfl

theorem secureOODDomain_card : secureOODDomain.card = P ^ 2 * (P ^ 2 - 1) := by
  have hnonzero : Fintype.card {z : CM31Exact // z ≠ 0} = P ^ 2 - 1 :=
    (Set.card_ne_eq (0 : CM31Exact)).trans
      (congrArg (fun n => n - 1) cm31_card)
  calc
    secureOODDomain.card = Fintype.card {z : QM31Exact // z.im ≠ 0} := by
      exact (Fintype.card_subtype (fun z : QM31Exact => z.im ≠ 0)).symm
    _ = Fintype.card (CM31Exact × {z : CM31Exact // z ≠ 0}) :=
      Fintype.card_congr secureOODEquiv
    _ = Fintype.card CM31Exact * Fintype.card {z : CM31Exact // z ≠ 0} :=
      Fintype.card_prod _ _
    _ = P ^ 2 * Fintype.card {z : CM31Exact // z ≠ 0} :=
      congrArg (fun n => n * Fintype.card {z : CM31Exact // z ≠ 0}) cm31_card
    _ = P ^ 2 * (P ^ 2 - 1) := congrArg (fun n => P ^ 2 * n) hnonzero

def sourceDomain (i : Fin 36) : Finset QM31Exact :=
  if i.val < 10 then fullQM31Domain
  else if i.val = 10 then nonzeroQM31Domain
  else if i.val = 11 then fullQM31Domain
  else if i.val = 12 ∨ i.val = 13 then secureOODDomain
  else fullQM31Domain

def sourceMinimum : Nat := P ^ 2 * (P ^ 2 - 1)

theorem sourceDomain_card_minimum (i : Fin 36) :
    sourceMinimum ≤ (sourceDomain i).card := by
  by_cases h0 : i.val < 10
  · rw [sourceDomain, if_pos h0, fullQM31Domain_card]
    norm_num [sourceMinimum, P]
  by_cases h10 : i.val = 10
  · rw [sourceDomain, if_neg h0, if_pos h10, nonzeroQM31Domain_card]
    norm_num [sourceMinimum, P]
  by_cases h11 : i.val = 11
  · rw [sourceDomain, if_neg h0, if_neg h10, if_pos h11,
      fullQM31Domain_card]
    norm_num [sourceMinimum, P]
  by_cases h1213 : i.val = 12 ∨ i.val = 13
  · rw [sourceDomain, if_neg h0, if_neg h10, if_neg h11,
      if_pos h1213, secureOODDomain_card]
    exact le_rfl
  · rw [sourceDomain, if_neg h0, if_neg h10, if_neg h11,
      if_neg h1213, fullQM31Domain_card]
    norm_num [sourceMinimum, P]

theorem fixed_root_domains_source (t : Fin 22 → QM31Exact)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1) :
    ((Finset.filter (fun s => eval s (determinantFor t ht noneOne) = 0)
        (Fintype.piFinset (sourceDomain))).card : ℚ≥0) /
        (∏ i, ((sourceDomain i).card : ℚ≥0)) ≤
      (819 : ℚ≥0) / sourceMinimum := by
  exact fixed_root_domains t ht noneOne sourceDomain sourceMinimum
    (by norm_num [sourceMinimum, P]) (sourceDomain_card_minimum)

#print axioms fullQM31Domain_card
#print axioms nonzeroQM31Domain_card
#print axioms imZero_card
#print axioms secureOODDomain_card
#print axioms fixed_root_domains_source
end
end AspisR19.TwoSwapSourceDomains
