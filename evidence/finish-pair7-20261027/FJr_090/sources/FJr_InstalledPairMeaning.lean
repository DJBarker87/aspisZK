import FJr_PairMeaning
import FJr_ConstructorInstallation
import FJr_InstallationOnRun
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJr_InstalledPairMeaning
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open AspisR1Stage2 AspisR1Stage2.Stage2Finish
open FIo_FieldBridge (NE wide)
open scoped BigOperators
attribute [local irreducible] QuadraticAlgebra.instInv

theorem value {C : Type} (err : C)
    (c : DrvC_Installation.Configuration FIo_Install.W C) (r : NP6_StdModel.Reservation) (semAlpha : Array K 10#usize)
    (z : Array aspis_core.circle.SecureCirclePoint 2#usize) (w : FIo_Install.W)
    (alpha : Slice AspisR1Stage2.Stage2Finish.E) (f : Slice U8)
    (kappa out : AspisR1Stage2.Stage2Finish.E)
    (hc : FJc_WeightArray.canonical (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ semAlpha))
    (cz : FJr_CircleOuterCell.CanonZ (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toPoint z))
    (hw : (FIp_Install.configuration err c r).finish.newWeights .S2 semAlpha z=ok (.Ok w))
    (folds : Slice.len (FIo_Install.toSlice alpha)=2#usize) (len : f.val.length=2048)
    (halpha : ∀ x∈(FIo_Install.toSlice alpha).val,FIo_WideValues.Canon x)
    (ckappa : FIo_WideValues.Canon (FIo_Install.toE kappa))
    (run : (FIp_Install.configuration err c r).finish.pair w alpha f kappa=ok (.Ok out)) :
    ∃ (a0 a1 : NE) (p0 p1 : FIn_WeightsExtract.circle.SecureCirclePoint),
      Slice.index_usize (FIo_Install.toSlice alpha) 0#usize=ok a0 ∧
      Slice.index_usize (FIo_Install.toSlice alpha) 1#usize=ok a1 ∧
      Array.index_usize (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toPoint z) 0#usize=ok p0 ∧
      Array.index_usize (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toPoint z) 1#usize=ok p1 ∧
      CheckpointBytes5Output.ofE out=RoundPairing.dot
        (fun i : Fin 64=>FJc_InactiveCoefficientsModel.field f i.val)
        (RoundPairing.dualFold (n:=64) (decodeWide (wide a1))
          (RoundPairing.dualFold (n:=256) (decodeWide (wide a0))
            (fun i=>∑ j : Fin 7,CheckpointBytes5Output.ofE kappa^j.val*FJr_PairRows.rows semAlpha p0 p1 j i))) := by
  have hw' : FIn_WeightsInstall.newWeights .S2 semAlpha z=ok (.Ok w) := by
    rw [FJr_ConstructorInstallation.weights] at hw
    exact hw
  have run' := FJr_InstallationOnRun.pair err c r w alpha f kappa out run
  exact FJr_PairMeaning.value r semAlpha z w alpha f kappa out hc cz hw' folds len halpha ckappa run'

#print axioms value
end AspisR1.FJr_InstalledPairMeaning
end
