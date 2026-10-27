import RPv_FJj_SuccessorDigit
import RPv_FJj_TensorPrefix
import RPv_FJj_ArrayReadTotal
import RPv_FJj_HighProductInstances
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJj_SuccessorHigh
open Aeneas Aeneas.Std Result
open AspisR1Stage2 AspisR1Stage2.Stage2Finish
open FIo_FieldBridge (NQ)
abbrev FK := OraclePortCheckpointAbiC5.K

def factors (alpha : Array K 10#usize) (d : Fin 5) (s : Fin 4) : FK :=
  FJd_PointReference.pointFactors
    (R0P.SemSource.successorPoint (FJf_ModelPoint.decoded
      (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ alpha))) d s

attribute [local irreducible] QuadraticAlgebra.instInv

theorem value (alpha : Array K 10#usize)
    (z : Array aspis_core.circle.SecureCirclePoint 2#usize) (w : FIo_Install.W)
    (hc : FJc_WeightArray.canonical (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ alpha))
    (hw : FIn_WeightsInstall.newWeights .S2 alpha z=ok (.Ok w))
    (row : Array (Array NQ 4#usize) 5#usize)
    (hr : Array.index_usize (FIo_Install.toWeights w).factors 1#usize=ok row) (i : Fin 64) :
    FJj_TensorPrefix.prefixValue (FJj_TensorPrefix.rowValue row) 3 i.val=
      FJg_TensorProduct.high (factors alpha) i := by
  obtain ⟨d2,h2⟩ := FJj_ArrayReadTotal.value row 2#usize (by decide)
  obtain ⟨d3,h3⟩ := FJj_ArrayReadTotal.value row 3#usize (by decide)
  obtain ⟨d4,h4⟩ := FJj_ArrayReadTotal.value row 4#usize (by decide)
  have v2 := (FJj_SuccessorDigit.value alpha z w hc hw 2#usize (by decide) row d2 hr h2).2
  have v3 := (FJj_SuccessorDigit.value alpha z w hc hw 3#usize (by decide) row d3 hr h3).2
  have v4 := (FJj_SuccessorDigit.value alpha z w hc hw 4#usize (by decide) row d4 hr h4).2
  have s2 : i.val%4<4 := Nat.mod_lt _ (by decide)
  have s3 : i.val/4%4<4 := Nat.mod_lt _ (by decide)
  have s4 : i.val/16<4 := by have := i.isLt;omega
  have r2 : ∀ s,FJj_TensorPrefix.rowValue row 2 s=FJf_QMArray.value d2 s := FJj_TensorPrefix.read row 2#usize d2 h2
  have r3 : ∀ s,FJj_TensorPrefix.rowValue row 3 s=FJf_QMArray.value d3 s := FJj_TensorPrefix.read row 3#usize d3 h3
  have r4 : ∀ s,FJj_TensorPrefix.rowValue row 4 s=FJf_QMArray.value d4 s := FJj_TensorPrefix.read row 4#usize d4 h4
  have q2 : FJf_QMArray.value d2 (i.val%4)=factors alpha 2 ⟨_,s2⟩ := v2 ⟨_,s2⟩
  have q3 : FJf_QMArray.value d3 (i.val/4%4)=factors alpha 3 ⟨_,s3⟩ := v3 ⟨_,s3⟩
  have q4 : FJf_QMArray.value d4 (i.val/16)=factors alpha 4 ⟨_,s4⟩ := v4 ⟨_,s4⟩
  have native : FJj_TensorPrefix.prefixValue (FJj_TensorPrefix.rowValue row) 3 i.val=
      FJj_HighProductInstances.product (factors alpha) i := by
    rw [FJj_TensorPrefix.three,r2,r3,r4,q2,q3,q4]
    rfl
  rw [native]
  exact FJj_HighProductInstances.tower AspisV8R15.ExactTowerBase.qm31R 0 (factors alpha) i
#print axioms value
end AspisR1.FJj_SuccessorHigh
end
