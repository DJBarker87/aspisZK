import AspisV8R19.R793MarkerTranspose
import AspisV8R19.R665FullSourceP2Boundary
import AspisV8R19.R740SparsePointObservation

/-! Full indexed ordinary source moment under explicit top-tail zeroes. -/
set_option autoImplicit false
namespace AspisV8R19.R851FullOrdinaryMoment

open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.TwoSwapSourceTable
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R740SparsePointObservation
open AspisV8R19.R788OrdinaryPointDecomposition
open AspisV8R19.R793MarkerTranspose
open AspisV8R19.R662FullIndexedMaskPreservation
open AspisV8R19.R665FullSourceP2Boundary
open scoped BigOperators
noncomputable section

variable {F : Type*} [Field F] [NeZero (2 : F)]

/-- With the four top flattened coordinates zero, the complete ordinary source
contraction retains exactly its three statement-point channels. -/
theorem ordinary_moment_of_top_zero
    (half a b c kappa tau : F) (z : Fin 10 → F) (q : Index256 → F)
    (hTop : ∀ r : Nat, 1020 ≤ r → rawFlatten q r = 0) :
    rangeDot 1024 (rawOrdinaryWeight half a b c kappa tau z) (rawFlatten q) =
      kappa * sourcePointFunctional (SourceStatementPoints.points z 0)
        (rawMask half a b c q) +
      kappa^2 * sourcePointFunctional (SourceStatementPoints.points z 1)
        (rawMask half a b c q) +
      kappa^3 * sourcePointFunctional (SourceStatementPoints.points z 2)
        (rawMask half a b c q) := by
  have hflat : rawFlatten q = flattenFull q := rawFlatten_eq_flattenFull q
  have hpoint (p : Fin 3) :
      rangeDot 1024 (pointWeight half a b c (SourceStatementPoints.points z p))
        (rawFlatten q) =
        sourcePointFunctional (SourceStatementPoints.points z p) (rawMask half a b c q) := by
    rw [hflat]
    exact (point_transport_pairing half a b c (SourceStatementPoints.points z p)
      (flattenFull q)).symm
  have hmarker (r : Nat) (hr : r < 1024) :
      sourceChordTranspose half marker a b c r * rawFlatten q r = 0 := by
    by_cases hbelow : r < 1021
    · rw [marker_transpose_zero_below half a b c hbelow]
      ring
    · have htop : 1020 ≤ r := by omega
      rw [hTop r htop]
      ring
  have himage (n : Nat) (x : F) (r : Nat) (hr : r < 1024) (hn : 1020 ≤ n) :
      (if r = n then x else 0) * rawFlatten q r = 0 := by
    by_cases h : r = n
    · subst r
      simp [hTop n hn]
    · simp [h]
  unfold rangeDot
  have hdecomp :
      (∑ i ∈ Finset.range 1024,
        rawOrdinaryWeight half a b c kappa tau z i * rawFlatten q i) =
      ∑ i ∈ Finset.range 1024,
        (kappa * pointWeight half a b c (SourceStatementPoints.points z 0) i +
          kappa^2 * pointWeight half a b c (SourceStatementPoints.points z 1) i +
          kappa^3 * pointWeight half a b c (SourceStatementPoints.points z 2) i) * rawFlatten q i := by
    apply Finset.sum_congr rfl
    intro i hi
    have hir : i < 1024 := Finset.mem_range.mp hi.2
    rw [raw_ordinary_weight_decomposition]
    have hm := hmarker i hir
    have hu23 := himage 1023 tau i hir (by omega)
    have hu22 := himage 1022 (tau^2*b) i hir (by omega)
    have hu21 := himage 1021 (tau^2*c) i hir (by omega)
    ring_nf at hm hu23 hu22 hu21 ⊢
    linear_combination hm + hu23 + hu22 - hu21
  rw [hdecomp]
  simp_rw [add_mul, mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hscale (x : F) (w : Nat → F) :
      (∑ i ∈ Finset.range 1024, x * w i * rawFlatten q i) =
        x * ∑ i ∈ Finset.range 1024, w i * rawFlatten q i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hscale kappa, hscale (kappa^2), hscale (kappa^3)]
  rw [hpoint 0, hpoint 1, hpoint 2]

#print axioms ordinary_moment_of_top_zero
end
end AspisV8R19.R851FullOrdinaryMoment
