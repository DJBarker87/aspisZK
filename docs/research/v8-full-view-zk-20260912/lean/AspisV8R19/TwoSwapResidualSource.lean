import AspisV8R19.TwoSwapResidualModel
import AspisV8R19.AugmentedQuotient

namespace AspisR19.TwoSwapResidualSource
open AspisV8R16 AspisV8R17 HighRepairInvariant BetaUniformCorrection TwoSwapSourceTable
open SourceGConstant TwoSwapSourceG TwoSwapSourceWeights
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

def querySection (t : Fin 22 → F) (ht : Function.Injective t) (noneOne : ∀ i, t i≠1) (j : Fin 13) : Fin 32 → F :=
  AugmentedQuerySection.normalized t ht noneOne (TwoSwapWitness.degree j)

theorem column_eq (t : Fin 22 → F) (ht : Function.Injective t) (noneOne : ∀ i, t i≠1) (alpha : F) (j : Fin 13) :
    TwoSwapResidualModel.column (querySection t ht noneOne) alpha j=AugmentedQuotient.quotient t ht noneOne alpha (TwoSwapWitness.degree j) (TwoSwapWitness.slot j) := by
  rfl

def originalWeight (half kappa : F) (z : Fin 10 → F) (previous : Fin 271 → F) (structured : Bool) : Fin 1024 → F :=
  sourceOriginalWeight (SourceStatementPoints.points z) kappa inactive
    (original (finishCoins half previous)) structured

theorem weight_eq (half a b c kappa : F) (z : Fin 10 → F) (previous : Fin 271 → F)
    (structured : Bool) (i : Index 32) :
    blockWeight half a b c (originalWeight half kappa z previous structured) i=
      TwoSwapResidualModel.weight half a b c kappa z structured i := by
  unfold originalWeight blockWeight
  rw [TwoSwapSourceG.source_point_weight]
  simp only [SourceStatementPoints.points_eq]
  cases structured
  · rfl
  · simp only [if_true]
    rw [TwoSwapSourceG.source_g_boundary]
    rfl

def quotientWeight (half a b c kappa tau : F) (z : Fin 10 → F)
    (previous : Fin 271 → F) (structured : Bool) : Nat → F :=
  sourceQuotientWeights half (extendFin1024 (transportDual inactive 1023 order
    (originalWeight half kappa z previous structured))) a b c tau structured

def relation (half quarter a b c kappa tau : F) (z : Fin 10 → F)
    (previous : Fin 271 → F) (structured : Bool) (q : Index 32 → F) (k : Nat) : F :=
  coefficient (sourceKernel 256 k quarter)
    (fun i => NormalizedGCore.flatten q (4*i.1.val+i.2.val))
    (fun i => quotientWeight half a b c kappa tau z previous structured (4*i.1.val+i.2.val))

theorem relation_eq (half quarter a b c kappa tau : F) (z : Fin 10 → F)
    (previous : Fin 271 → F) (structured : Bool) (q : Index 32 → F) (k : Nat) :
    relation half quarter a b c kappa tau z previous structured q k=
      coefficient (sourceKernel 32 k quarter) q (TwoSwapResidualModel.weight half a b c kappa z structured) := by
  rw [relation,quotientWeight,source_coefficient,funext (weight_eq half a b c kappa z previous structured)]

theorem point_eq (half a b c : F) (z : Fin 10 → F) (q : Index 32 → F) (which : Fin 3) :
    sourcePointFunctional (SourceStatementPoints.points z which) (mask half a b c q)=
      ∑ i : Index 32,q i*TwoSwapResidualModel.pointWeight half a b c z which.val i := by
  rw [source_point,SourceStatementPoints.points_eq]
  rfl

def observed (half quarter a b c kappa tau : F) (z : Fin 10 → F)
    (previous : Fin 271 → F) (q : Index 32 → F) (row : Nat) : F :=
  if h : row<3 then sourcePointFunctional (SourceStatementPoints.points z ⟨row,h⟩) (mask half a b c q)
  else if row<10 then relation half quarter a b c kappa tau z previous false q (row-3)
  else relation half quarter a b c kappa tau z previous true q (row-10)

theorem observed_eq (half quarter a b c kappa tau : F) (z : Fin 10 → F)
    (previous : Fin 271 → F) (q : Index 32 → F) (row : Nat) :
    observed half quarter a b c kappa tau z previous q row=
      TwoSwapResidualModel.observed half quarter a b c kappa z q row := by
  unfold observed TwoSwapResidualModel.observed
  split_ifs
  · exact point_eq half a b c z q _
  · exact relation_eq half quarter a b c kappa tau z previous false q _
  · exact relation_eq half quarter a b c kappa tau z previous true q _

def matrix (half quarter a b c kappa alpha tau : F) (z : Fin 10 → F)
    (previous : Fin 271 → F) (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i≠1) : Matrix (Fin 13) (Fin 13) F :=
  fun i j => observed half quarter a b c kappa tau z previous
    (AugmentedQuotient.quotient t ht noneOne alpha (TwoSwapWitness.degree j) (TwoSwapWitness.slot j)) (ResidualModel.selectedRow i)

theorem matrix_eq (half quarter a b c kappa alpha tau : F) (z : Fin 10 → F)
    (previous : Fin 271 → F) (t : Fin 22 → F) (ht : Function.Injective t) (noneOne : ∀ i, t i≠1) :
    matrix half quarter a b c kappa alpha tau z previous t ht noneOne=
      TwoSwapResidualModel.matrix half quarter a b c kappa alpha z (querySection t ht noneOne) := by
  funext i j
  simp only [matrix,TwoSwapResidualModel.matrix,observed_eq,column_eq]

#print axioms column_eq
#print axioms weight_eq
#print axioms relation_eq
#print axioms point_eq
#print axioms observed_eq
#print axioms matrix_eq
end
end AspisR19.TwoSwapResidualSource
