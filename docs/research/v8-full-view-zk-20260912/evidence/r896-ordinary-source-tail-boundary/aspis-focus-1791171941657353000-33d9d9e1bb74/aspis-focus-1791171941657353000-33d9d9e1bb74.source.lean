import AspisV8R19.R851FullOrdinaryMoment

/-! Exact ordinary source boundary retaining the marker and image-tail terms. -/
set_option autoImplicit false
namespace AspisV8R19.R896OrdinarySourceTailBoundary

open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.TwoSwapSourceTable
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R740SparsePointObservation
open AspisV8R19.R788OrdinaryPointDecomposition
open AspisV8R19.R793MarkerTranspose
open AspisV8R19.R665FullSourceP2Boundary
open AspisV8R19.R662FullIndexedMaskPreservation
open scoped BigOperators
noncomputable section

variable {F : Type*} [Field F] [NeZero (2 : F)]

private theorem point_pairing (half a b c : F) (z : Fin 10 → F)
    (q : Index256 → F) (p : Fin 3) :
    rangeDot 1024 (pointWeight half a b c (SourceStatementPoints.points z p))
      (rawFlatten q) =
      sourcePointFunctional (SourceStatementPoints.points z p) (rawMask half a b c q) := by
  rw [rawFlatten_eq_flattenFull]
  exact (point_transport_pairing half a b c (SourceStatementPoints.points z p)
    (flattenFull q)).symm

/-- The exact ordinary `c0+c4` source boundary.  Unlike the earlier
four-coordinate-tail corollary, this keeps the marker and all literal image
updates visible. -/
theorem ordinary_source_tail_boundary
    (half quarter a b c kappa tau : F) (z : Fin 10 → F) (q : Index256 → F) :
    rawRelation half quarter a b c kappa tau z q 0 +
        rawRelation half quarter a b c kappa tau z q 4 =
      quarter *
        (kappa * sourcePointFunctional (SourceStatementPoints.points z 0) (rawMask half a b c q) +
          kappa^2 * sourcePointFunctional (SourceStatementPoints.points z 1) (rawMask half a b c q) +
          kappa^3 * sourcePointFunctional (SourceStatementPoints.points z 2) (rawMask half a b c q) +
          rangeDot 1024 (sourceChordTranspose half marker a b c) (rawFlatten q) +
          tau * rawFlatten q 1023 +
          tau^2 * (b * rawFlatten q 1022 - c * rawFlatten q 1021)) := by
  unfold rawRelation
  rw [AspisV8R19.R653SourceCoefficientBoundary.coefficient_boundary 256 quarter q
    (fun i => rawOrdinaryWeight half a b c kappa tau z (4 * i.1.val + i.2.val))]
  have hpair := full_flatten_pairing q (rawOrdinaryWeight half a b c kappa tau z)
  rw [← hpair]
  rw [show flattenFull q = rawFlatten q by
    exact (rawFlatten_eq_flattenFull q).symm]
  have hdecomp :
      rangeDot 1024 (rawOrdinaryWeight half a b c kappa tau z) (rawFlatten q) =
        kappa * rangeDot 1024 (pointWeight half a b c (SourceStatementPoints.points z 0)) (rawFlatten q) +
        kappa^2 * rangeDot 1024 (pointWeight half a b c (SourceStatementPoints.points z 1)) (rawFlatten q) +
        kappa^3 * rangeDot 1024 (pointWeight half a b c (SourceStatementPoints.points z 2)) (rawFlatten q) +
        rangeDot 1024 (sourceChordTranspose half marker a b c) (rawFlatten q) +
        tau * rawFlatten q 1023 + tau^2 * b * rawFlatten q 1022 - tau^2 * c * rawFlatten q 1021 := by
    unfold rangeDot
    rw [show (∑ i ∈ Finset.range 1024,
        rawOrdinaryWeight half a b c kappa tau z i * rawFlatten q i) =
        ∑ i ∈ Finset.range 1024,
          (kappa * pointWeight half a b c (SourceStatementPoints.points z 0) i +
            kappa^2 * pointWeight half a b c (SourceStatementPoints.points z 1) i +
            kappa^3 * pointWeight half a b c (SourceStatementPoints.points z 2) i +
            sourceChordTranspose half marker a b c i +
            (if i = 1023 then tau else 0) +
            (if i = 1022 then tau^2 * b else 0) -
            (if i = 1021 then tau^2 * c else 0)) * rawFlatten q i by
      apply Finset.sum_congr rfl
      intro i _
      rw [raw_ordinary_weight_decomposition]]
    simp only [add_mul, sub_mul]
    rw [Finset.sum_sub_distrib]
    repeat' rw [Finset.sum_add_distrib]
    have hscale (x : F) (w : Nat → F) :
        (∑ i ∈ Finset.range 1024, (x * w i) * rawFlatten q i) =
          x * ∑ i ∈ Finset.range 1024, w i * rawFlatten q i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hscale kappa, hscale (kappa^2), hscale (kappa^3)]
    rw [Finset.sum_ite_eq' (s := Finset.range 1024) (a := 1023) (by decide),
      Finset.sum_ite_eq' (s := Finset.range 1024) (a := 1022) (by decide),
      Finset.sum_ite_eq' (s := Finset.range 1024) (a := 1021) (by decide)]
    ring
  rw [hdecomp, point_pairing half a b c z q 0,
    point_pairing half a b c z q 1, point_pairing half a b c z q 2]
  ring

/-- The genuine source quotient-image tails remove only their own two image
updates; the marker contraction remains explicit. -/
theorem ordinary_source_boundary_of_image_tails
    (half quarter a b c kappa tau : F) (z : Fin 10 → F) (q : Index256 → F)
    (h23 : rawFlatten q 1023 = 0)
    (himage : b * rawFlatten q 1022 - c * rawFlatten q 1021 = 0) :
    rawRelation half quarter a b c kappa tau z q 0 +
        rawRelation half quarter a b c kappa tau z q 4 =
      quarter *
        (kappa * sourcePointFunctional (SourceStatementPoints.points z 0) (rawMask half a b c q) +
          kappa^2 * sourcePointFunctional (SourceStatementPoints.points z 1) (rawMask half a b c q) +
          kappa^3 * sourcePointFunctional (SourceStatementPoints.points z 2) (rawMask half a b c q) +
          rangeDot 1024 (sourceChordTranspose half marker a b c) (rawFlatten q)) := by
  rw [ordinary_source_tail_boundary, h23, himage]
  ring

#print axioms ordinary_source_tail_boundary
#print axioms ordinary_source_boundary_of_image_tails
end
end AspisV8R19.R896OrdinarySourceTailBoundary