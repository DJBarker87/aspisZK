import AspisV8R19.SourceFixedResidual

namespace AspisR19.FullWeightHom
open AspisV8R17 RootCertificate T163SourceTable FullPointFunctional FullQuotientWeights
open FullCoefficientBoundary SourceGConstant SparseGScatter OriginalChannelWeights
noncomputable section
variable {F G : Type*} [CommRing F] [CommRing G]

theorem map_weight (f : F →+* G) (half a b c : F) (w : Fin 1024 → F) (r : Fin 128) :
    f (pointWeight half a b c w r)=
      pointWeight (f half) (f a) (f b) (f c) (fun i => f (w i)) r := by
  simp only [pointWeight,codeWeight,map_sum,map_mul,map_sub,apply_ite,map_zero,
    ResidualModel.map_chordEntry]

theorem map_point_basis (f : F →+* G) (z : Fin 10 → F) (which : Nat) (r : Nat) :
    f (sourcePointBasis (ResidualModel.point z which) r)=
      sourcePointBasis (ResidualModel.point (fun i => f (z i)) which) r := by
  simp only [source_tensor,ResidualModel.tensor,map_prod,apply_ite,map_sub,map_one,
    ResidualModel.map_point]

theorem fixed_point (f : M →+* F) (which : Fin 3) (r : Fin 128) :
    pointWeight (f half) (f 7) (f 5) (f (-5))
      (fun i => sourcePointBasis (ResidualModel.point (fun j => f (SparseHighWitness.z j)) which.val) i.val) r=
      f (SparseHighWitness.ew which.val r.val) := by
  have h := congrArg f (FullWitnessPointCode.full_point_specialization which r)
  simpa only [map_weight,map_point_basis] using h

theorem fixed_channels (f : M →+* F) (previous : Fin 271 → F) (structured : Bool)
    (i : HighRepairInvariant.Index 32) :
    blockWeight (f half) (f 7) (f 5) (f (-5))
      (sourceOriginalWeight
        (fun which => ResidualModel.point (fun j => f (SparseHighWitness.z j)) which.val)
        (f 5) inactive (original (finishCoins (f half) previous)) structured) i=
      f (if structured then SparseHighWitness.wg i else SparseHighWitness.wr i) := by
  unfold blockWeight
  rw [source_point_weight,fixed_point f (1:Fin 3),fixed_point f (2:Fin 3)]
  cases structured
  · simp only [Bool.false_eq_true,if_false]
    rw [fixed_point f (0:Fin 3)]
    simp only [SparseHighWitness.wr,SparseHighWitness.e,map_add,map_mul,map_pow]
    rfl
  · simp only [if_true]
    rw [source_g_boundary]
    simp only [SparseHighWitness.wg,SparseHighWitness.e,SparseHighWitness.hg,
      map_add,map_mul,map_pow,ResidualModel.map_chordEntry,
      show (1:Fin 3).val=1 by rfl,show (2:Fin 3).val=2 by rfl]
    ring

#print axioms map_weight
#print axioms map_point_basis
#print axioms fixed_point
#print axioms fixed_channels
end
end AspisR19.FullWeightHom
