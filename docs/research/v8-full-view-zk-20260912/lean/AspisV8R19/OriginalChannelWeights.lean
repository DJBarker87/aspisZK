import AspisV8R19.SourceGConstant

namespace AspisR19.OriginalChannelWeights
open AspisV8R17 T163SourceTable FullPointFunctional FullQuotientWeights
open FullCoefficientBoundary SourceGConstant SparseGScatter RootCertificate
noncomputable section
variable {F : Type*} [CommRing F]

theorem source_code (points : Fin 3 → Fin 10 → F) (kappa : F)
    (g : Fin 1024 → F) (structured : Bool) (j : Fin 131) :
    codeWeight (sourceOriginalWeight points kappa inactive g structured) j=
      kappa*(if structured then codeWeight g j else
        codeWeight (fun r => sourcePointBasis (points 0) r.val) j)+
      kappa^2*codeWeight (fun r => sourcePointBasis (points 1) r.val) j+
      kappa^3*codeWeight (fun r => sourcePointBasis (points 2) r.val) j := by
  have hp := pivot_inactive
  have hj : order (lowIndex j)∈inactive ↔ isInactive (order (lowIndex j))=true := by
    simp [inactive]
  cases structured <;> simp only [codeWeight,sourceOriginalWeight_eq,Bool.false_eq_true,
    Bool.true_eq,if_true,if_false,hp,hj]
  all_goals split_ifs <;> ring

theorem source_point_weight (points : Fin 3 → Fin 10 → F) (kappa half a b c : F)
    (g : Fin 1024 → F) (structured : Bool) (r : Fin 128) :
    pointWeight half a b c (sourceOriginalWeight points kappa inactive g structured) r=
      kappa*(if structured then pointWeight half a b c g r else
        pointWeight half a b c (fun i => sourcePointBasis (points 0) i.val) r)+
      kappa^2*pointWeight half a b c (fun i => sourcePointBasis (points 1) i.val) r+
      kappa^3*pointWeight half a b c (fun i => sourcePointBasis (points 2) i.val) r := by
  simp only [pointWeight,source_code,add_mul,mul_assoc,Finset.sum_add_distrib,← Finset.mul_sum]
  cases structured <;> rfl

theorem fixed_channels (previous : Fin 271 → M) (structured : Bool)
    (i : HighRepairInvariant.Index 32) :
    blockWeight half (7:M) 5 (-5)
      (sourceOriginalWeight (fun which => ResidualModel.point SparseHighWitness.z which.val)
        5 inactive (original (finishCoins half previous)) structured) i=
      if structured then SparseHighWitness.wg i else SparseHighWitness.wr i := by
  unfold blockWeight
  rw [source_point_weight]
  rw [FullWitnessPointCode.full_point_specialization (1:Fin 3),
    FullWitnessPointCode.full_point_specialization (2:Fin 3)]
  cases structured
  · simp only [Bool.false_eq_true,if_false]
    rw [FullWitnessPointCode.full_point_specialization (0:Fin 3)]
    rfl
  · simp only [Bool.true_eq,if_true]
    rw [source_g_boundary]
    unfold SparseHighWitness.wg SparseHighWitness.e SparseHighWitness.hg
    simp only [show (1:Fin 3).val=1 by rfl,show (2:Fin 3).val=2 by rfl]
    ring

#print axioms source_code
#print axioms source_point_weight
#print axioms fixed_channels
end
end AspisR19.OriginalChannelWeights
