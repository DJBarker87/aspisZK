import AspisV8R19.R793MarkerTranspose
import AspisV8R19.R741SparseCoefficientObservation

/-! Ordinary source coefficient rows retain exactly their three point-weight terms below updates. -/
set_option autoImplicit false
namespace AspisV8R19.R795OrdinaryCoefficientDecomposition

open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.TwoSwapSourceTable
open AspisV8R19.R788OrdinaryPointDecomposition
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R793MarkerTranspose
open AspisV8R19.R740SparsePointObservation
open AspisV8R19.R741SparseCoefficientObservation
open scoped BigOperators
noncomputable section

variable {F : Type*} [CommRing F]

theorem raw_ordinary_weight_below
    (half a b c kappa tau : F) (z : Fin 10 → F) {r : Nat} (hr : r < 1021) :
    rawOrdinaryWeight half a b c kappa tau z r =
      kappa * pointWeight half a b c (SourceStatementPoints.points z 0) r +
        kappa^2 * pointWeight half a b c (SourceStatementPoints.points z 1) r +
        kappa^3 * pointWeight half a b c (SourceStatementPoints.points z 2) r := by
  rw [raw_ordinary_weight_decomposition]
  rw [marker_transpose_zero_below half a b c hr]
  have h1023 : r ≠ 1023 := by omega
  have h1022 : r ≠ 1022 := by omega
  have h1021 : r ≠ 1021 := by omega
  simp [h1023, h1022, h1021]

theorem rowWeight_raw_ordinary_decomposition
    (half a b c kappa tau quarter : F) (z : Fin 10 → F)
    (d : Fin 255) (slot : Fin 4) (k : Nat) :
    rowWeight 256 k quarter
      (fun i => rawOrdinaryWeight half a b c kappa tau z (4*i.1.val+i.2.val))
      (cast255 d) slot =
      kappa * rowWeight 256 k quarter
        (fun i => pointWeight half a b c (SourceStatementPoints.points z 0)
          (4*i.1.val+i.2.val)) (cast255 d) slot +
      kappa^2 * rowWeight 256 k quarter
        (fun i => pointWeight half a b c (SourceStatementPoints.points z 1)
          (4*i.1.val+i.2.val)) (cast255 d) slot +
      kappa^3 * rowWeight 256 k quarter
        (fun i => pointWeight half a b c (SourceStatementPoints.points z 2)
          (4*i.1.val+i.2.val)) (cast255 d) slot := by
  unfold rowWeight
  have hbound (t : Fin 4) : 4 * (cast255 d).val + t.val < 1021 := by
    simp only [cast255]
    omega
  calc
    (∑ t : Fin 4, (if slot.val + (4 - t.val) % 4 = k then quarter else 0) *
        rawOrdinaryWeight half a b c kappa tau z (4 * (cast255 d).val + t.val)) =
      ∑ t : Fin 4, (if slot.val + (4 - t.val) % 4 = k then quarter else 0) *
        (kappa * pointWeight half a b c (SourceStatementPoints.points z 0)
            (4 * (cast255 d).val + t.val) +
          kappa^2 * pointWeight half a b c (SourceStatementPoints.points z 1)
            (4 * (cast255 d).val + t.val) +
          kappa^3 * pointWeight half a b c (SourceStatementPoints.points z 2)
            (4 * (cast255 d).val + t.val)) := by
        apply Finset.sum_congr rfl
        intro t _
        rw [raw_ordinary_weight_below half a b c kappa tau z (hbound t)]
    _ = kappa * (∑ t : Fin 4, (if slot.val + (4 - t.val) % 4 = k then quarter else 0) *
          pointWeight half a b c (SourceStatementPoints.points z 0)
            (4 * (cast255 d).val + t.val)) +
        kappa^2 * (∑ t : Fin 4, (if slot.val + (4 - t.val) % 4 = k then quarter else 0) *
          pointWeight half a b c (SourceStatementPoints.points z 1)
            (4 * (cast255 d).val + t.val)) +
        kappa^3 * (∑ t : Fin 4, (if slot.val + (4 - t.val) % 4 = k then quarter else 0) *
          pointWeight half a b c (SourceStatementPoints.points z 2)
            (4 * (cast255 d).val + t.val)) := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        have sum_scale (x : F) (w : Nat → F) :
            (∑ t : Fin 4, (if slot.val + (4 - t.val) % 4 = k then quarter else 0) *
              (x * w (4 * (cast255 d).val + t.val))) =
              x * (∑ t : Fin 4, (if slot.val + (4 - t.val) % 4 = k then quarter else 0) *
                w (4 * (cast255 d).val + t.val)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro t _
          ring
        rw [sum_scale kappa, sum_scale (kappa^2), sum_scale (kappa^3)]
    _ = _ := by rfl

#print axioms raw_ordinary_weight_below
#print axioms rowWeight_raw_ordinary_decomposition

end
end AspisV8R19.R795OrdinaryCoefficientDecomposition
