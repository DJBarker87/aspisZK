import RPv_FJm_AbsorptionDigit
import RPv_FJj_LowSum
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJm_AbsorptionScale
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open AspisR1Stage2 AspisR1Stage2.Stage2Finish
open FIo_FieldBridge (NQ NE wide)
open scoped BigOperators
def factors (alpha : Array K 10#usize) (d : Fin 5) (s : Fin 4) : OraclePortCheckpointAbiC5.K :=
  FJd_PointReference.pointFactors (R0P.SemSource.xor12Point (FJf_ModelPoint.decoded
    (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ alpha))) d s

attribute [local irreducible] QuadraticAlgebra.instInv FJg_DualTensor.low

theorem value (alpha : Array K 10#usize)
    (z : Array aspis_core.circle.SecureCirclePoint 2#usize) (w : FIo_Install.W)
    (hc : FJc_WeightArray.canonical (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ alpha))
    (hw : FIn_WeightsInstall.newWeights .S2 alpha z=ok (.Ok w))
    (d : Usize) (db : d.val<5) (row : Array (Array NQ 4#usize) 5#usize) (digit : Array NQ 4#usize)
    (hr : Array.index_usize (FIo_Install.toWeights w).factors 2#usize=ok row)
    (hd : Array.index_usize row d=ok digit)
    (a : NE) (p : Array NE 4#usize) (ha : FIo_WideValues.Canon a)
    (hp : FIo_Native.weights.powers 4#usize a=ok p) :
    decodeM FIo_Native.weights.QUARTER • FJg_ScalarCell.sumPrefix p digit 4=
      FJg_DualTensor.low
        (fun s=>algebraMap OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E (factors alpha ⟨d.val,db⟩ s))
        (decodeWide (wide a)) := by
  have powers := FIp_PowersValue.powers 4#usize a p ha hp
  have sum : FJg_ScalarCell.sumPrefix p digit 4=∑ s : Fin 4,FJg_ScalarCell.term p digit s.val := by
    rw [FJg_ScalarReference.sumPrefix,Fin.sum_univ_eq_sum_range]
  have terms : FJg_ScalarCell.sumPrefix p digit 4=∑ s : Fin 4,
      algebraMap OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E (factors alpha ⟨d.val,db⟩ s)*
        decodeWide (wide a)^((4-s.val)%4) := by
    rw [sum]
    apply Finset.sum_congr rfl
    intro s _
    rw [FJg_ScalarCell.term,powers.2 _ (FJc_PermTable.bound s.val s.isLt)]
    have digitValues := FJm_AbsorptionDigit.value alpha z w hc hw
      d db row digit hr hd
    rw [digitValues.2 s,FJg_Permutation.value]
    unfold factors
    ring
  rw [terms]
  exact FJj_LowSum.value _ _
#print axioms value
end AspisR1.FJm_AbsorptionScale
end
