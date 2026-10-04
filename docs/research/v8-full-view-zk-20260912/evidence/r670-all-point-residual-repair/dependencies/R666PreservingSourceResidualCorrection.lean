import AspisV8R19.R665FullSourceP2Boundary
set_option autoImplicit false
namespace AspisV8R19.R666PreservingSourceResidualCorrection
open AspisR19 AspisV8R17 HighRepairInvariant BetaUniformCorrection
open R645TwoSwapHighDirections R649TwoSwapResidualRepair
open R660FullSourceResidualCorrection R662FullIndexedMaskPreservation R665FullSourceP2Boundary
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

/-- Full-support conditional correction with every beta retained, exact full
source p2 moment, and the combined G mask's sparse/point/balance observations.
This leaves actual H1 active-preserving construction, native bindings, query
and determinant laws, and published-view privacy/security unproved. -/
theorem full_source_preserving_residual_correction (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i ≠ 1) (half quarter a b c kappa alpha tau scale : F)
    (z : Fin 10 → F) (previous : Fin 271 → F) (r g0 : Index 256 → F)
    (hquarter : quarter ≠ 0) (hscale : scale ≠ 0)
    (hf : ∀ d, R370KernelEvaluation.firstFold 256 alpha r d = 0)
    (hfg : ∀ d, R370KernelEvaluation.firstFold 256 alpha g0 d = 0)
    (hr : ∀ k : Fin 7, fullRelation half quarter a b c kappa tau z previous false r k.val = 0)
    (hg : ∀ k : Fin 7, fullRelation half quarter a b c kappa tau z previous true g0 k.val = 0)
    (hdet : (TwoSwapResidualSource.matrix half quarter a b c kappa alpha tau z
      previous t ht noneOne).det ≠ 0) :
    ∃ x : Fin 13 → F,
      (∀ beta : F, ∀ k : Fin 7,
        coefficient (sourceKernel 256 k.val quarter)
          (fun i => (1-beta)*r i + scale*beta*(g0 i + extendCorrection (combination t ht noneOne alpha x) i))
          (fun i => (1-beta)*fullWeight half a b c kappa tau z previous false i +
            beta*fullWeight half a b c kappa tau z previous true i) = 0) ∧
      (scale * (rangeDot 1024 (TwoSwapResidualSource.quotientWeight half a b c kappa tau z previous true)
        (flattenFull (fun j => g0 j+extendCorrection (combination t ht noneOne alpha x) j)) -
        rangeDot 1024 (TwoSwapResidualSource.quotientWeight half a b c kappa tau z previous false)
        (flattenFull (fun j => g0 j+extendCorrection (combination t ht noneOne alpha x) j))) -
        (rangeDot 1024 (TwoSwapResidualSource.quotientWeight half a b c kappa tau z previous true) (flattenFull r) -
        rangeDot 1024 (TwoSwapResidualSource.quotientWeight half a b c kappa tau z previous false) (flattenFull r)) = 0) ∧
      (∀ i : Fin 271, actualCoin (indexedMask half a b c
        (fun j => g0 j+extendCorrection (combination t ht noneOne alpha x) j)) i =
        actualCoin (indexedMask half a b c g0) i) ∧
      (∀ i : Fin 2, sourcePointFunctional (SourceStatementPoints.points z ⟨i.val+1,by omega⟩)
        (indexedMask half a b c (fun j => g0 j+extendCorrection (combination t ht noneOne alpha x) j)) =
        sourcePointFunctional (SourceStatementPoints.points z ⟨i.val+1,by omega⟩) (indexedMask half a b c g0)) ∧
      ((∑ v ∈ TwoSwapSourceTable.inactive, indexedMask half a b c
        (fun j => g0 j+extendCorrection (combination t ht noneOne alpha x) j) v) =
        ∑ v ∈ TwoSwapSourceTable.inactive, indexedMask half a b c g0 v) ∧
      (∀ slot : Fin 4, ∀ root : Fin 22, NormalizedQuerySection.evaluate
        (fun d => combination t ht noneOne alpha x (d,slot)) (t root) = 0) ∧
      (∀ d : Fin 32, R370KernelEvaluation.firstFold 32 alpha
        (combination t ht noneOne alpha x) d = 0) := by
  obtain ⟨x,hquad,hpoints,hcoins,hqueries,hfold,hbalance⟩ :=
    full_source_residual_correction t ht noneOne half quarter a b c kappa alpha tau scale
      z previous r g0 hscale hf hfg hr hg hdet
  refine ⟨x,hquad,?_,?_,?_,?_,hqueries,hfold⟩
  · exact full_source_p2 half quarter a b c kappa tau scale z previous r
      (fun j => g0 j+extendCorrection (combination t ht noneOne alpha x) j) hquarter hscale hquad
  · exact indexed_sparse_coins_preserved t ht noneOne half alpha a b c x g0
  · intro i
    exact indexed_point_preserved half a b c g0 (combination t ht noneOne alpha x)
      (SourceStatementPoints.points z ⟨i.val+1,by omega⟩) (hpoints i)
  · exact indexed_balance_preserved t ht noneOne half alpha a b c x g0

#print axioms full_source_preserving_residual_correction
end
end AspisV8R19.R666PreservingSourceResidualCorrection
