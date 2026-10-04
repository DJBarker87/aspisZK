import AspisV8R19.R653SourceCoefficientBoundary
import Mathlib.Tactic
set_option autoImplicit false
namespace AspisV8R19.R664FullMomentP2
open AspisR19 BetaUniformCorrection
open R653SourceCoefficientBoundary
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

private theorem coefficient_components {I J : Type*} [Fintype I] [Fintype J]
    (C : I → J → F) (scale : F) (hscale : scale ≠ 0)
    (r g : I → F) (wR wG : J → F)
    (hquad : ∀ beta : F, coefficient C
      (fun i => (1-beta)*r i+scale*beta*g i)
      (fun j => (1-beta)*wR j+beta*wG j)=0) :
    coefficient C r wR = 0 ∧
    coefficient C r wG + scale*coefficient C g wR = 0 ∧
    coefficient C g wG = 0 := by
  have hr := hquad 0
  have hg := hquad 1
  have htwo := (NeZero.ne (2 : F))
  have h2 := hquad 2
  have hr' : coefficient C r wR = 0 := by
    simpa using hr
  have hg' : coefficient C g wG = 0 := by
    change coefficient C (fun i => scale * g i) wG = 0 at hg
    rw [coefficient_left C g (fun _ => 0) wG scale 0] at hg
    simp only [mul_zero, add_zero] at hg
    exact (mul_eq_zero.mp hg).resolve_left hscale
  have hcross : coefficient C r wG + scale*coefficient C g wR = 0 := by
    change coefficient C (fun i => -r i + (scale*2)*g i)
      (fun j => -wR j + 2*wG j) = 0 at h2
    rw [coefficient_left C (fun i => -r i) g _ 1 (scale*2)] at h2
    rw [coefficient_right C (fun i => -r i) wR wG (-1) 2] at h2
    rw [coefficient_right C g wR wG (-1) 2] at h2
    simp only [coefficient_left C r (fun _ => 0) wR (-1) 0,
      coefficient_left C r (fun _ => 0) wG (-1) 0,
      mul_zero, add_zero] at h2
    have h : - (2 * (coefficient C r wG + scale * coefficient C g wR)) = 0 := by
      calc
        _ = coefficient C (fun i => -r i + (scale*2)*g i)
          (fun j => -wR j + 2*wG j) := by
            rw [coefficient_left, coefficient_right, coefficient_right]
            rw [hr', hg']
            ring
        _ = 0 := h2
    exact neg_eq_zero.mp ((mul_eq_zero.mp (neg_mul_eq_neg_mul_one.mpr h)).resolve_left htwo)
  exact ⟨hr',hcross,hg'⟩

theorem full_moment_p2 (n : Nat) (quarter scale : F)
    (hquarter : quarter ≠ 0) (hscale : scale ≠ 0)
    (r g wR wG : Fin n × Fin 4 → F)
    (hquad : ∀ beta : F, ∀ k : Fin 7, coefficient (sourceKernel n k.val quarter)
      (fun i => (1-beta)*r i+scale*beta*g i)
      (fun j => (1-beta)*wR j+beta*wG j)=0) :
    scale*((∑ d : Fin n, ∑ s : Fin 4, g (d,s)*wG (d,s))-
      (∑ d : Fin n, ∑ s : Fin 4, g (d,s)*wR (d,s)))-
      ((∑ d : Fin n, ∑ s : Fin 4, r (d,s)*wG (d,s))-
      (∑ d : Fin n, ∑ s : Fin 4, r (d,s)*wR (d,s)))=0 := by
  have comp (k : Fin 7) := coefficient_components (sourceKernel n k.val quarter)
    scale hscale r g wR wG (fun beta => hquad beta k)
  obtain ⟨hr0,hc0,hg0⟩ := comp 0
  obtain ⟨hr4,hc4,hg4⟩ := comp 4
  have hmR : (∑ d : Fin n, ∑ s : Fin 4, r (d,s)*wR (d,s))=0 := by
    have h := coefficient_boundary n quarter r wR
    rw [hr0,hr4,zero_add] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hquarter
  have hmG : (∑ d : Fin n, ∑ s : Fin 4, g (d,s)*wG (d,s))=0 := by
    have h := coefficient_boundary n quarter g wG
    rw [hg0,hg4,zero_add] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hquarter
  have hmC : (∑ d : Fin n, ∑ s : Fin 4, r (d,s)*wG (d,s))+
      scale*(∑ d : Fin n, ∑ s : Fin 4, g (d,s)*wR (d,s))=0 := by
    have h := coefficient_boundary n quarter r wG
    have hg := coefficient_boundary n quarter g wR
    rw [← Finset.mul_add, ← Finset.sum_add_distrib] at h hg
    have hc : coefficient (sourceKernel n 0 quarter) r wG+
        scale*coefficient (sourceKernel n 0 quarter) g wR+
        (coefficient (sourceKernel n 4 quarter) r wG+
        scale*coefficient (sourceKernel n 4 quarter) g wR)=0 := by
      rw [hc0,hc4]
      ring
    rw [h,hg] at hc
    exact (mul_eq_zero.mp hc).resolve_left hquarter
  exact p2_retained _ _ _ _ scale hmR hmC hmG

#print axioms full_moment_p2
end
end AspisV8R19.R664FullMomentP2
