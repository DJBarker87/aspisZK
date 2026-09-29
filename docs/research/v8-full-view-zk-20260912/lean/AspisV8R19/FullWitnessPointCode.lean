import AspisV8R19.FullResidualBoundary

/-! Reuse the old sparse point certificate only after proving the 20 newly
retained coordinates are zero at that specialization. No generic cutoff is
asserted, and the sparse-G boundary at 128 is a different functional. -/
namespace AspisR19.FullWitnessPointCode
open AspisV8R17 FullPointFunctional FullQuotientWeights RootCertificate
noncomputable section
variable {F : Type*} [CommRing F]

theorem old_code_agrees (z : Fin 10 → F) (j : Fin 111) :
    codeWeight (fun r => sourcePointBasis z r.val) ⟨j.val,by omega⟩=
      ResidualModel.codeWeight ResidualPins.order ResidualPins.inactive z j := by
  simp only [codeWeight,source_tensor,lowIndex,ResidualModel.codeWeight]
  rw [T163SourceTable.residual_order_agrees j,T163SourceTable.residual_inactive_agrees j]
  rfl

theorem extra_point_zero (which : Fin 3) (j : Fin 20) :
    tensorCode (ResidualModel.point SparseHighWitness.z which.val) (Fin.natAdd 111 j)=0 := by
  fin_cases which <;> fin_cases j <;> decide

theorem point_agrees (which : Fin 3) (r : Fin 128) :
    pointWeight half (7:M) 5 (-5)
      (fun i => sourcePointBasis (ResidualModel.point SparseHighWitness.z which.val) i.val) r=
    ResidualModel.pointWeight ResidualPins.order ResidualPins.inactive half (7:M) 5 (-5)
      SparseHighWitness.z which.val r.val := by
  unfold pointWeight
  rw [Fin.sum_univ_add (a:=111) (b:=20)]
  have hz : (∑ j : Fin 20,
      codeWeight (fun i => sourcePointBasis (ResidualModel.point SparseHighWitness.z which.val) i.val)
        (Fin.natAdd 111 j)*ResidualModel.chordEntry half (7:M) 5 (-5) r.val (Fin.natAdd 111 j).val)=0 := by
    apply Finset.sum_eq_zero
    intro j _
    have h := extra_point_zero which j
    have he : codeWeight
        (fun i => sourcePointBasis (ResidualModel.point SparseHighWitness.z which.val) i.val)
        (Fin.natAdd 111 j)=tensorCode (ResidualModel.point SparseHighWitness.z which.val) (Fin.natAdd 111 j) := by
      simp only [codeWeight,tensorCode,source_tensor]
      rfl
    rw [he,h,zero_mul]
  rw [hz,add_zero]
  unfold ResidualModel.pointWeight
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun v => v*ResidualModel.chordEntry half (7:M) 5 (-5) r.val j.val)
    (old_code_agrees (ResidualModel.point SparseHighWitness.z which.val) j)

theorem full_point_specialization (which : Fin 3) (r : Fin 128) :
    pointWeight half (7:M) 5 (-5)
      (fun i => sourcePointBasis (ResidualModel.point SparseHighWitness.z which.val) i.val) r=
      SparseHighWitness.ew which.val r.val := by
  rw [point_agrees]
  fin_cases which
  · exact SparseHighWitness.point0_weight r.val
  · exact SparseHighWitness.point1_weight r.val
  · exact SparseHighWitness.point2_weight r.val

#print axioms old_code_agrees
#print axioms extra_point_zero
#print axioms point_agrees
#print axioms full_point_specialization
end
end AspisR19.FullWitnessPointCode
