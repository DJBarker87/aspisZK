import AspisV8R19.OriginalChannelWeights
import AspisV8R19.SourceStatementPoints
import AspisV8R19.HighWitnessTransport
import AspisV8R15.ExactTowerBase

/-! The source-shaped ordinary/G observations at the algebraic witness now
use the retained inverse certificate. This is not an accepted-prefix law. -/
namespace AspisR19.SourceFixedResidual
open AspisV8R16 AspisV8R17 RootCertificate T163SourceTable HighRepairInvariant
open SourceMaskTransport FullQuotientWeights FullCoefficientBoundary FullResidualBoundary
open BetaUniformCorrection SourceGConstant SparseGScatter OriginalChannelWeights
noncomputable section
local instance : Fact (Nat.Prime 2147483647) := AspisV8R15.ExactTowerBase.m31PrimeFact
local instance : NeZero (2 : M) := ⟨by decide⟩

def originalWeight (previous : Fin 271 → M) (structured : Bool) : Fin 1024 → M :=
  sourceOriginalWeight (SourceStatementPoints.points SparseHighWitness.z) 5 inactive
    (original (finishCoins half previous)) structured

theorem weight_eq (previous : Fin 271 → M) (structured : Bool) (i : Index 32) :
    blockWeight half (7:M) 5 (-5) (originalWeight previous structured) i=
      if structured then SparseHighWitness.wg i else SparseHighWitness.wr i := by
  have hp : SourceStatementPoints.points SparseHighWitness.z=
      fun which => ResidualModel.point SparseHighWitness.z which.val := by
    funext which
    exact SourceStatementPoints.points_eq _ which
  rw [originalWeight,hp]
  exact fixed_channels previous structured i

def quotientWeight (previous : Fin 271 → M) (tau : M) (structured : Bool) : Nat → M :=
  sourceQuotientWeights half (extendFin1024 (transportDual inactive 1023 order
    (originalWeight previous structured))) 7 5 (-5) tau structured

def relation (previous : Fin 271 → M) (tau : M) (structured : Bool)
    (q : Index 32 → M) (k : Nat) : M :=
  coefficient (sourceKernel 256 k (536870912:M))
    (fun i => NormalizedGCore.flatten q (4*i.1.val+i.2.val))
    (fun i => quotientWeight previous tau structured (4*i.1.val+i.2.val))

theorem relation_eq (previous : Fin 271 → M) (tau : M) (structured : Bool)
    (q : Index 32 → M) (k : Nat) :
    relation previous tau structured q k=
      coefficient (sourceKernel 32 k (536870912:M)) q
        (if structured then SparseHighWitness.wg else SparseHighWitness.wr) := by
  rw [relation,quotientWeight,source_coefficient]
  have hw := funext (weight_eq previous structured)
  rw [hw]
  cases structured <;> rfl

theorem point_eq (q : Index 32 → M) (which : Fin 3) :
    sourcePointFunctional (SourceStatementPoints.points SparseHighWitness.z which)
      (mask half (7:M) 5 (-5) q)=∑ i : Index 32,q i*SparseHighWitness.e which.val i := by
  rw [source_point,SourceStatementPoints.points_eq]
  apply Finset.sum_congr rfl
  intro i _
  unfold blockWeight
  rw [FullWitnessPointCode.full_point_specialization]
  rfl

def observed (previous : Fin 271 → M) (tau : M) (q : Index 32 → M) (row : Nat) : M :=
  if h : row<3 then sourcePointFunctional
    (SourceStatementPoints.points SparseHighWitness.z ⟨row,h⟩) (mask half (7:M) 5 (-5) q)
  else if row<10 then relation previous tau false q (row-3)
  else relation previous tau true q (row-10)

theorem observed_eq (previous : Fin 271 → M) (tau : M) (q : Index 32 → M) (row : Nat) :
    observed previous tau q row=HighWitnessTransport.observed q row := by
  unfold observed HighWitnessTransport.observed
  split_ifs
  · exact point_eq q _
  · simpa using relation_eq previous tau false q (row-3)
  · simpa using relation_eq previous tau true q (row-10)

def matrix (previous : Fin 271 → M) (tau : M) (t : Fin 22 → M) : Matrix (Fin 13) (Fin 13) M :=
  fun i j => observed previous tau (SourceCircleBoundary.column t 7 j) (ResidualModel.selectedRow i)

theorem matrix_equal (previous : Fin 271 → M) (tau : M) (t : Fin 22 → M)
    (ht : Function.Injective t) : matrix previous tau t=SparseHighWitness.matrix := by
  have he : matrix previous tau t=HighWitnessTransport.matrix (SourceCircleBoundary.column t 7) := by
    funext i j
    exact observed_eq previous tau _ _
  rw [he]
  apply HighWitnessTransport.matrix_equal
  intro j i hi
  rw [SourceCircleBoundary.column,NormalizationLoopBridge.selected_sourceQuotient_eq t ht 7 j]
  exact NormalizedQuotient.quotient_high t ht 7 _ _ i hi

theorem det_ne_zero (previous : Fin 271 → M) (tau : M) (t : Fin 22 → M)
    (ht : Function.Injective t) : (matrix previous tau t).det≠0 := by
  rw [matrix_equal previous tau t ht]
  exact HighWitnessData.model_det_ne_zero

#print axioms weight_eq
#print axioms relation_eq
#print axioms point_eq
#print axioms observed_eq
#print axioms matrix_equal
#print axioms det_ne_zero
end
end AspisR19.SourceFixedResidual
