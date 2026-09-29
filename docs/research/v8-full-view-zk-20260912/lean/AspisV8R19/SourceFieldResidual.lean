import AspisV8R19.FullWeightHom
import AspisV8R19.HighWitnessFieldTransport
import AspisV8R19.QM31ResidualWitness

/-! Fixed source-shaped residuals over the exact field, with arbitrary query
roots. The specialization is algebraic, not asserted to be sampled. -/
namespace AspisR19.SourceFieldResidual
open AspisV8R16 AspisV8R17 RootCertificate T163SourceTable HighRepairInvariant
open SourceMaskTransport FullCoefficientBoundary FullResidualBoundary BetaUniformCorrection
open SourceGConstant SparseGScatter FullWeightHom
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

def originalWeight (f : M →+* F) (previous : Fin 271 → F) (structured : Bool) : Fin 1024 → F :=
  sourceOriginalWeight (SourceStatementPoints.points (fun i => f (SparseHighWitness.z i))) (f 5) inactive
    (original (finishCoins (f half) previous)) structured

theorem weight_eq (f : M →+* F) (previous : Fin 271 → F) (structured : Bool) (i : Index 32) :
    blockWeight (f half) (f 7) (f 5) (f (-5)) (originalWeight f previous structured) i=
      f (if structured then SparseHighWitness.wg i else SparseHighWitness.wr i) := by
  have hp := funext (SourceStatementPoints.points_eq (fun i => f (SparseHighWitness.z i)))
  rw [originalWeight,hp]
  exact FullWeightHom.fixed_channels f previous structured i

def quotientWeight (f : M →+* F) (previous : Fin 271 → F) (tau : F) (structured : Bool) : Nat → F :=
  sourceQuotientWeights (f half) (extendFin1024 (transportDual inactive 1023 order
    (originalWeight f previous structured))) (f 7) (f 5) (f (-5)) tau structured

def relation (f : M →+* F) (previous : Fin 271 → F) (tau : F) (structured : Bool)
    (q : Index 32 → F) (k : Nat) : F :=
  coefficient (sourceKernel 256 k (f 536870912))
    (fun i => NormalizedGCore.flatten q (4*i.1.val+i.2.val))
    (fun i => quotientWeight f previous tau structured (4*i.1.val+i.2.val))

theorem relation_eq (f : M →+* F) (previous : Fin 271 → F) (tau : F) (structured : Bool)
    (q : Index 32 → F) (k : Nat) :
    relation f previous tau structured q k=
      coefficient (sourceKernel 32 k (f 536870912)) q
        (fun i => f (if structured then SparseHighWitness.wg i else SparseHighWitness.wr i)) := by
  rw [relation,quotientWeight,source_coefficient,funext (weight_eq f previous structured)]

theorem point_eq (f : M →+* F) (q : Index 32 → F) (which : Fin 3) :
    sourcePointFunctional (SourceStatementPoints.points (fun i => f (SparseHighWitness.z i)) which)
      (mask (f half) (f 7) (f 5) (f (-5)) q)=∑ i : Index 32,q i*f (SparseHighWitness.e which.val i) := by
  rw [source_point,SourceStatementPoints.points_eq]
  apply Finset.sum_congr rfl
  intro i _
  unfold blockWeight
  rw [FullWeightHom.fixed_point]
  rfl

def observed (f : M →+* F) (previous : Fin 271 → F) (tau : F) (q : Index 32 → F) (row : Nat) : F :=
  if h : row<3 then sourcePointFunctional
    (SourceStatementPoints.points (fun i => f (SparseHighWitness.z i)) ⟨row,h⟩)
      (mask (f half) (f 7) (f 5) (f (-5)) q)
  else if row<10 then relation f previous tau false q (row-3)
  else relation f previous tau true q (row-10)

theorem observed_eq (f : M →+* F) (previous : Fin 271 → F) (tau : F) (q : Index 32 → F) (row : Nat) :
    observed f previous tau q row=HighWitnessFieldTransport.observed f q row := by
  unfold observed HighWitnessFieldTransport.observed
  split_ifs
  · exact point_eq f q _
  · simpa using relation_eq f previous tau false q (row-3)
  · simpa using relation_eq f previous tau true q (row-10)

def matrix (f : M →+* F) (previous : Fin 271 → F) (tau : F) (t : Fin 22 → F) : Matrix (Fin 13) (Fin 13) F :=
  fun i j => observed f previous tau (SourceCircleBoundary.column t (f 7) j) (ResidualModel.selectedRow i)

theorem column_high (f : M →+* F) (t : Fin 22 → F) (ht : Function.Injective t)
    (j : Fin 13) (i : Index 32) (hi : 22 ≤ i.1.val) :
    SourceCircleBoundary.column t (f 7) j i=
      f (HighRepairInvariant.column (7:M) (SparseHighWitness.degree j) (SparseHighWitness.slot j) i) := by
  rw [SourceCircleBoundary.column,NormalizationLoopBridge.selected_sourceQuotient_eq t ht (f 7) j,
    NormalizedQuotient.quotient_high t ht (f 7) _ _ i hi]
  simp only [HighRepairInvariant.column,unit,map_sub,map_mul,map_pow]
  split_ifs <;> simp_all

theorem matrix_equal (f : M →+* F) (previous : Fin 271 → F) (tau : F) (t : Fin 22 → F)
    (ht : Function.Injective t) : matrix f previous tau t=SparseHighWitness.matrix.map f := by
  have he : matrix f previous tau t=HighWitnessFieldTransport.matrix f (SourceCircleBoundary.column t (f 7)) := by
    funext i j
    exact observed_eq f previous tau _ _
  rw [he]
  exact HighWitnessFieldTransport.matrix_equal f _ (column_high f t ht)

theorem det_ne_zero (f : M →+* F) (hf : Function.Injective f)
    (previous : Fin 271 → F) (tau : F) (t : Fin 22 → F) (ht : Function.Injective t) :
    (matrix f previous tau t).det≠0 := by
  rw [matrix_equal f previous tau t ht]
  change (f.mapMatrix SparseHighWitness.matrix).det≠0
  rw [← f.map_det]
  intro h
  apply HighWitnessData.model_det_ne_zero
  apply hf
  simpa only [map_zero] using h

open AspisV8R15.ExactTowerBase QM31ResidualWitness
local instance : NeZero (2 : QM31Exact) := ⟨by
  intro h
  have hz : (2:M)=0 := embed_injective (by simpa only [map_ofNat,map_zero] using h)
  exact (by decide : (2:M)≠0) hz⟩

theorem exact_qm31 (previous : Fin 271 → QM31Exact) (tau : QM31Exact)
    (t : Fin 22 → QM31Exact) (ht : Function.Injective t) :
    (matrix embed previous tau t).det≠0 :=
  det_ne_zero embed embed_injective previous tau t ht

#print axioms weight_eq
#print axioms relation_eq
#print axioms point_eq
#print axioms observed_eq
#print axioms column_high
#print axioms matrix_equal
#print axioms det_ne_zero
#print axioms exact_qm31
end
end AspisR19.SourceFieldResidual
