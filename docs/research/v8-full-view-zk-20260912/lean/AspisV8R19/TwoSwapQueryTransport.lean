import AspisV8R19.AugmentedQuotient
import AspisV8R19.TwoSwapLowWeights
import AspisV8R19.TwoSwapNonzero

/-! For the fixed new-profile weight model, the same 13x13 residual minor
is invertible for every distinct 22-root tuple excluding 1. This is not a
law for the shared oracle, a full C1/H1/G coverage theorem, or a Rust word
refinement. The field is an arbitrary target of the base-field embedding. -/
set_option autoImplicit false
namespace AspisR19.TwoSwapQueryTransport
open RootCertificate HighRepairInvariant BetaUniformCorrection TwoSwapWitness
noncomputable section

theorem point_low (which : Fin 3) (i : Fin 32) (hi : i.val<23) (s : Fin 4) :
    pointBlock which.val (i,s)=pointBlock which.val (0,s) := by
  fin_cases which
  · simpa [pointBlock] using point_low0 ⟨i.val,hi⟩ s
  · simpa [pointBlock] using point_low1 ⟨i.val,hi⟩ s
  · simpa [pointBlock] using point_low2 ⟨i.val,hi⟩ s

theorem channel_low (which : Fin 2) (i : Fin 32) (hi : i.val<23) (s : Fin 4) :
    channelBlock which.val (i,s)=channelBlock which.val (0,s) := by
  fin_cases which
  · simpa [channelBlock] using channel_low0 ⟨i.val,hi⟩ s
  · simpa [channelBlock] using channel_low1 ⟨i.val,hi⟩ s

theorem basis_low (s : Fin 4) (i : Fin 32) (hi : i.val<23) (row : Nat) :
    basisObservation s i row=basisObservation s 0 row := by
  have hc0 (b : Fin 4) : channelBlock 0 (i,b)=channelBlock 0 (0,b) :=
    channel_low (0:Fin 2) i hi b
  have hc1 (b : Fin 4) : channelBlock 1 (i,b)=channelBlock 1 (0,b) :=
    channel_low (1:Fin 2) i hi b
  unfold basisObservation
  split_ifs with h
  · rw [point_low ⟨row,h⟩ i hi s,point_low ⟨row,h⟩ i hi 0]
  · simp only [localCoeff,hc0]
  · simp only [localCoeff,hc1]

variable {F : Type*} [Field F] [NeZero (2 : F)]

def observed (f : M →+* F) (s : Fin 4) (v : Fin 32 → F) (row : Nat) : F :=
  ∑ i, v i * f (basisObservation s i row)

theorem observed_point (f : M →+* F) (s : Fin 4) (v : Fin 32 → F) (row : Fin 3) :
    (∑ i, AugmentedQuotient.lift (f 7) s v i * f (pointBlock row.val i))=
      observed f s v row.val := by
  rw [AugmentedQuotient.lift_point]
  simp [observed,basisObservation,row.isLt]

theorem observed_relation (f : M →+* F) (s : Fin 4) (v : Fin 32 → F)
    (which : Fin 2) (k : Fin 7) :
    coefficient (sourceKernel 32 k.val (f 536870912))
      (AugmentedQuotient.lift (f 7) s v) (fun i => f (channelBlock which.val i))=
      observed f s v (3+7*which.val+k.val) := by
  rw [AugmentedQuotient.lift_coefficient]
  have hk:=k.isLt
  fin_cases which <;>
    simp [observed,basisObservation,show ¬3+k.val<3 by omega,
      show 3+k.val<10 by omega,show ¬3+7+k.val<3 by omega,
      show ¬3+7+k.val<10 by omega,localCoeff,apply_ite]

theorem normalized_observed (f : M →+* F) (s : Fin 4)
    (t : Fin 22 → F) (ht : Function.Injective t) (noneOne : ∀ i, t i≠1)
    (d : Fin 32) (row : Nat) :
    observed f s (AugmentedQuerySection.normalized t ht noneOne d) row =
      f (basisObservation s d row-basisObservation s 0 row) := by
  rw [map_sub]
  exact AugmentedQuerySection.constant_low_transport t ht noneOne d _
    (fun i hi => congrArg f (basis_low s i hi row))

def normalizedMatrix (f : M →+* F) (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i≠1) : Matrix (Fin 13) (Fin 13) F := fun i j =>
  observed f (slot j) (AugmentedQuerySection.normalized t ht noneOne (degree j))
    (ResidualModel.selectedRow i)

theorem normalized_matrix (f : M →+* F) (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i≠1) : normalizedMatrix f t ht noneOne=TwoSwapWitness.matrix.map f := by
  funext i j
  exact normalized_observed f (slot j) t ht noneOne (degree j) _

theorem normalized_right_inverse (f : M →+* F) (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i≠1) :
    normalizedMatrix f t ht noneOne * inverseMatrix.map f = 1 := by
  rw [normalized_matrix,matrix_entries,← RingHom.mapMatrix_apply,
    ← RingHom.mapMatrix_apply,← map_mul,right_inverse,map_one]

theorem normalized_det_ne_zero (f : M →+* F) (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i≠1) : (normalizedMatrix f t ht noneOne).det≠0 :=
  ResidualNonsingular.right_inverse_det_ne_zero _ _ (normalized_right_inverse f t ht noneOne)

#print axioms point_low
#print axioms channel_low
#print axioms basis_low
#print axioms observed_point
#print axioms observed_relation
#print axioms normalized_observed
#print axioms normalized_matrix
#print axioms normalized_right_inverse
#print axioms normalized_det_ne_zero
end
end AspisR19.TwoSwapQueryTransport
