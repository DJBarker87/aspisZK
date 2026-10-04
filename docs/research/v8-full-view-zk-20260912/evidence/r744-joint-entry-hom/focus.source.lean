import AspisV8R19.R742SourceObservationHom
import AspisV8R19.R743JointSparseEntryBinding

/-! Ring-map naturality for the point and ordinary-coefficient entries of the
R743 sparse observation.  The active chord branch is intentionally absent. -/
set_option autoImplicit false
namespace AspisV8R19.R744JointEntryHom
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R742SourceObservationHom
open AspisV8R19.R743JointSparseEntryBinding
open AspisV8R19.R741SparseCoefficientObservation
open scoped BigOperators
noncomputable section
variable {F K : Type*} [CommRing F] [CommRing K]

theorem map_rowWeight (f : F →+* K) (n k : Nat) (quarter : F)
    (w : Fin n × Fin 4 → F) (d : Fin n) (slot : Fin 4) :
    f (rowWeight n k quarter w d slot) =
      rowWeight n k (f quarter) (fun i => f (w i)) d slot := by
  unfold rowWeight
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro t _
  split <;> simp only [map_mul, map_zero]

theorem map_sparse_point_row (f : F →+* K) (half quarter a b c kappa tau alpha : F)
    (z : Fin 10 → F) (d : Fin 255) (s : Fin 3) (p : Fin 3) :
    f (sparseObservation half quarter a b c kappa tau alpha z d s (.inr (.inl p))) =
      sparseObservation (f half) (f quarter) (f a) (f b) (f c) (f kappa) (f tau)
        (f alpha) (fun i => f (z i)) d s (.inr (.inl p)) := by
  simp only [sparseObservation, map_sub, map_mul, map_pow]
  rw [map_pointWeight f half a b c (SourceStatementPoints.points z p) (4*d.val+s.val+1),
    map_pointWeight f half a b c (SourceStatementPoints.points z p) (4*d.val),
    map_pointWeight f half a b c (SourceStatementPoints.points z p) (s.val+1),
    map_pointWeight f half a b c (SourceStatementPoints.points z p) 0]
  simp only [map_points]

theorem map_sparse_coefficient_row (f : F →+* K) (half quarter a b c kappa tau alpha : F)
    (z : Fin 10 → F) (d : Fin 255) (s : Fin 3) (k : Fin 5) :
    f (sparseObservation half quarter a b c kappa tau alpha z d s (.inr (.inr k))) =
      sparseObservation (f half) (f quarter) (f a) (f b) (f c) (f kappa) (f tau)
        (f alpha) (fun i => f (z i)) d s (.inr (.inr k)) := by
  simp only [sparseObservation, map_sub, map_mul, map_pow]
  repeat' rw [map_rowWeight]
  congr 4 <;> funext i <;>
    exact map_rawOrdinaryWeight f half a b c kappa tau z (4*i.1.val+i.2.val)

#print axioms map_rowWeight
#print axioms map_sparse_point_row
#print axioms map_sparse_coefficient_row
end
end AspisV8R19.R744JointEntryHom
