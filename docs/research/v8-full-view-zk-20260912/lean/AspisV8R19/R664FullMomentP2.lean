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
  have zero_left (w : J → F) : coefficient C (fun _ => 0) w = 0 := by
    simp [coefficient]
  have hg' : coefficient C g wG = 0 := by
    simp only [sub_self, zero_mul, mul_one, zero_add, one_mul] at hg
    have hs := coefficient_left C g (fun _ => 0) wG scale 0
    rw [zero_left] at hs
    have hs' : coefficient C (fun i => scale * g i) wG =
        scale * coefficient C g wG := by simpa using hs
    rw [hs'] at hg
    exact (mul_eq_zero.mp hg).resolve_left hscale
  have neg_left (q : I → F) (w : J → F) :
      coefficient C (fun i => -q i) w = -coefficient C q w := by
    have h := coefficient_left C q (fun _ => 0) w (-1) 0
    rw [zero_left] at h
    simpa only [neg_one_mul, mul_zero, add_zero] using h
  have right_two (q : I → F) :
      coefficient C q (fun j => -wR j + 2*wG j) =
        -coefficient C q wR+2*coefficient C q wG := by
    have h := coefficient_right C q wR wG (-1) 2
    simpa only [neg_one_mul] using h
  have hcross : coefficient C r wG + scale*coefficient C g wR = 0 := by
    have hone : (1-(2:F)) = -1 := by ring
    simp only [hone, neg_one_mul] at h2
    have left_two : coefficient C (fun i => -r i + (scale*2)*g i)
        (fun j => -wR j + 2*wG j) =
        coefficient C (fun i => -r i) (fun j => -wR j + 2*wG j)+
          (scale*2)*coefficient C g (fun j => -wR j + 2*wG j) := by
      have h := coefficient_left C (fun i => -r i) g
        (fun j => -wR j + 2*wG j) 1 (scale*2)
      simpa only [one_mul] using h
    rw [left_two, right_two, right_two, neg_left, neg_left] at h2
    rw [hr', hg'] at h2
    have h : - (2 * (coefficient C r wG + scale * coefficient C g wR)) = 0 := by
      linear_combination h2
    have h' : 2 * (coefficient C r wG + scale * coefficient C g wR) = 0 :=
      neg_eq_zero.mp h
    exact (mul_eq_zero.mp h').resolve_left htwo
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
  have h0 := comp (0 : Fin 7)
  have h4 := comp (4 : Fin 7)
  have hr0 : coefficient (sourceKernel n 0 quarter) r wR = 0 := by simpa using h0.1
  have hc0 : coefficient (sourceKernel n 0 quarter) r wG +
      scale*coefficient (sourceKernel n 0 quarter) g wR = 0 := by simpa using h0.2.1
  have hg0 : coefficient (sourceKernel n 0 quarter) g wG = 0 := by simpa using h0.2.2
  have hr4 : coefficient (sourceKernel n 4 quarter) r wR = 0 := by simpa using h4.1
  have hc4 : coefficient (sourceKernel n 4 quarter) r wG +
      scale*coefficient (sourceKernel n 4 quarter) g wR = 0 := by simpa using h4.2.1
  have hg4 : coefficient (sourceKernel n 4 quarter) g wG = 0 := by simpa using h4.2.2
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
    have hrG := coefficient_boundary n quarter r wG
    have hgR := coefficient_boundary n quarter g wR
    have hc : coefficient (sourceKernel n 0 quarter) r wG +
        coefficient (sourceKernel n 4 quarter) r wG +
        scale*(coefficient (sourceKernel n 0 quarter) g wR +
          coefficient (sourceKernel n 4 quarter) g wR)=0 := by
      calc
        _ = (coefficient (sourceKernel n 0 quarter) r wG +
          scale*coefficient (sourceKernel n 0 quarter) g wR) +
          (coefficient (sourceKernel n 4 quarter) r wG +
          scale*coefficient (sourceKernel n 4 quarter) g wR) := by ring
        _ = 0 := by rw [hc0,hc4]; ring
    rw [hrG,hgR] at hc
    ring_nf at hc
    have hc' : quarter * ((∑ d : Fin n, ∑ s : Fin 4, r (d,s)*wG (d,s))+
        scale*(∑ d : Fin n, ∑ s : Fin 4, g (d,s)*wR (d,s))) = 0 := by
      convert hc using 1 <;> ring
    exact (mul_eq_zero.mp hc').resolve_left hquarter
  exact p2_retained _ _ _ _ scale hmR hmC hmG

#print axioms full_moment_p2
end
end AspisV8R19.R664FullMomentP2
