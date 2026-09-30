import AspisV8R19.TwoSwapResidualSource
import AspisV8R19.TwoSwapQueryTransport

/-! Source-shaped point and complete channel observations specialize to the
R120 minor for every permitted root tuple. This is a fixed challenge witness,
not a claim that the real adaptive sampler has a particular conditional law. -/
set_option autoImplicit false
namespace AspisR19.TwoSwapSourceMinor
open AspisV8R17 HighRepairInvariant RootCertificate TwoSwapResidualSource
noncomputable section
variable {F : Type*} [Field F] [NeZero (2:F)]

theorem fixed_weight (f : M →+* F) (structured : Bool) (i : Index 32) :
    TwoSwapResidualModel.weight (f half) (f 7) (f 5) (f (-5)) (f 5)
      (fun j => f (TwoSwapWitness.z j)) structured i=
      f (TwoSwapWitness.channelBlock (if structured then 1 else 0) i) := by
  rw [← weight_eq _ _ _ _ _ _ (fun _ => 0) structured i]
  unfold TwoSwapSourceWeights.blockWeight originalWeight
  rw [funext (SourceStatementPoints.points_eq (fun j => f (TwoSwapWitness.z j)))]
  exact TwoSwapSourceFixed.fixed_channel f (fun _ => 0) structured _

theorem fixed_observed (f : M →+* F) (s : Fin 4) (v : Fin 32 → F) (row : Fin 17) :
    TwoSwapResidualModel.observed (f half) (f 536870912) (f 7) (f 5) (f (-5)) (f 5)
      (fun j => f (TwoSwapWitness.z j)) (AugmentedQuotient.lift (f 7) s v) row.val=
      TwoSwapQueryTransport.observed f s v row.val := by
  unfold TwoSwapResidualModel.observed
  split_ifs with h3 h10
  · have he (i : Index 32) :
        TwoSwapResidualModel.pointWeight (f half) (f 7) (f 5) (f (-5))
          (fun j => f (TwoSwapWitness.z j)) row.val i=f (TwoSwapWitness.pointBlock row.val i) :=
      TwoSwapSourceFixed.fixed_point f ⟨row.val,h3⟩ _
    simp only [he]
    exact TwoSwapQueryTransport.observed_point f s v ⟨row.val,h3⟩
  · rw [funext (fixed_weight f false)]
    have h:=TwoSwapQueryTransport.observed_relation f s v (0:Fin 2) ⟨row.val-3,by omega⟩
    simpa only [show (0:Fin 2).val=0 by rfl,Nat.mul_zero,Nat.add_zero,
      show 3+(row.val-3)=row.val by omega,Bool.false_eq_true,if_false] using h
  · rw [funext (fixed_weight f true)]
    have h:=TwoSwapQueryTransport.observed_relation f s v (1:Fin 2) ⟨row.val-10,by omega⟩
    simpa only [show (1:Fin 2).val=1 by rfl,Nat.mul_one,
      show 3+7+(row.val-10)=row.val by omega,if_true] using h

theorem selected_bound (i : Fin 13) : ResidualModel.selectedRow i<17 := by
  fin_cases i <;> decide

theorem matrix_fixed (f : M →+* F) (previous : Fin 271 → F) (tau : F)
    (t : Fin 22 → F) (ht : Function.Injective t) (noneOne : ∀ i,t i≠1) :
    matrix (f half) (f 536870912) (f 7) (f 5) (f (-5)) (f 5) (f 7) tau
      (fun j => f (TwoSwapWitness.z j)) previous t ht noneOne=
      TwoSwapQueryTransport.normalizedMatrix f t ht noneOne := by
  funext i j
  rw [matrix,observed_eq]
  exact fixed_observed f (TwoSwapWitness.slot j)
    (AugmentedQuerySection.normalized t ht noneOne (TwoSwapWitness.degree j))
    ⟨ResidualModel.selectedRow i,selected_bound i⟩

theorem determinant_nonzero (f : M →+* F) (previous : Fin 271 → F) (tau : F)
    (t : Fin 22 → F) (ht : Function.Injective t) (noneOne : ∀ i,t i≠1) :
    (matrix (f half) (f 536870912) (f 7) (f 5) (f (-5)) (f 5) (f 7) tau
      (fun j => f (TwoSwapWitness.z j)) previous t ht noneOne).det≠0 := by
  rw [matrix_fixed]
  exact TwoSwapQueryTransport.normalized_det_ne_zero f t ht noneOne

#print axioms fixed_weight
#print axioms fixed_observed
#print axioms selected_bound
#print axioms matrix_fixed
#print axioms determinant_nonzero
end
end AspisR19.TwoSwapSourceMinor
