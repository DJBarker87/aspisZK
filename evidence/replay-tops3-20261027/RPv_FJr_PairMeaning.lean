import RPv_FJr_PairParts
import RPv_FJr_FinalSumModel
import RPv_FIo_ConcreteDictionary
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJr_PairMeaning
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open AspisR1Stage2 AspisR1Stage2.Stage2Finish
open FIo_FieldBridge (NE wide)
open scoped BigOperators
attribute [local irreducible] QuadraticAlgebra.instInv

theorem value (r : NP6_StdModel.Reservation) (semAlpha : Array K 10#usize)
    (z : Array aspis_core.circle.SecureCirclePoint 2#usize) (w : FIo_Install.W)
    (alpha : Slice AspisR1Stage2.Stage2Finish.E) (f : Slice U8)
    (kappa out : AspisR1Stage2.Stage2Finish.E)
    (hc : FJc_WeightArray.canonical (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ semAlpha))
    (cz : FJr_CircleOuterCell.CanonZ (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toPoint z))
    (hw : FIn_WeightsInstall.newWeights .S2 semAlpha z=ok (.Ok w))
    (folds : Slice.len (FIo_Install.toSlice alpha)=2#usize) (len : f.val.length=2048)
    (halpha : ∀ x∈(FIo_Install.toSlice alpha).val,FIo_WideValues.Canon x)
    (ckappa : FIo_WideValues.Canon (FIo_Install.toE kappa))
    (run : FIo_Install.pair r w alpha f kappa=ok (.Ok out)) :
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
  letI := FIo_Install.allocation r
  obtain ⟨nativeOut,he,⟨t⟩⟩ := FJr_PairTrace.reached r semAlpha z w alpha f kappa out hc hw folds len run
  obtain ⟨p0,p1,hz0,hz1,canon,values⟩ := FJr_PairParts.value r semAlpha z w hc cz hw
    (FIo_Install.toSlice alpha) f (FIo_Install.toE kappa) nativeOut t len halpha
  have summed := FJr_FinalSumModel.value t.parts t.k (FIo_Install.toE kappa) nativeOut canon ckappa
    t.powersK t.sum (FJr_PairRows.rows semAlpha p0 p1)
    (fun i : Fin 64=>FJc_InactiveCoefficientsModel.field f i.val)
    (decodeWide (wide t.a0)) (decodeWide (wide t.a1)) values
  have kvalue : decodeWide (wide (FIo_Install.toE kappa))=CheckpointBytes5Output.ofE kappa := by
    simpa only [FIo_Install.from_to] using (FIo_ConcreteDictionary.decoded (FIo_Install.toE kappa)).symm
  rw [kvalue] at summed
  refine ⟨t.a0,t.a1,p0,p1,t.read0,t.read1,hz0,hz1,?_⟩
  rw [←he,FIo_ConcreteDictionary.decoded]
  exact summed.2

#print axioms value
end AspisR1.FJr_PairMeaning
end
