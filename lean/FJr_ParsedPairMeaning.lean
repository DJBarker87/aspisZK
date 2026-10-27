import FJr_PairMeaning
import FJr_AlphaPrefix
import FJg_ReadSemanticCanon
import FJg_ReaderScalarCanon
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJr_ParsedPairMeaning
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open AspisR1Stage2 AspisR1Stage2.Stage2Finish
open FIo_FieldBridge (NE wide)
open scoped BigOperators
attribute [local irreducible] QuadraticAlgebra.instInv

theorem value {N : Usize} (r : NP6_StdModel.Reservation) (semAlpha : Array K 10#usize)
    (z : Array aspis_core.circle.SecureCirclePoint 2#usize) (w : FIo_Install.W)
    (alpha : Slice AspisR1Stage2.Stage2Finish.E) (f : Slice U8)
    (kappa out : AspisR1Stage2.Stage2Finish.E)
    (cz : FJr_CircleOuterCell.CanonZ (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toPoint z))
    (hw : FIn_WeightsInstall.newWeights .S2 semAlpha z=ok (.Ok w))
    (len : f.val.length=2048)
    (bytes : Slice U8) (start stop : Usize)
    (semanticRead : (T2Nat_ReaderOps.ops true).readSemanticAlpha bytes start=ok (.Ok (semAlpha,stop)))
    (point : Array AspisR1Stage2.Stage2Finish.E N) (bound : 2≤N.val)
    (cp : ∀ x∈point.val,FIo_WideValues.Canon (FIo_Install.toE x))
    (prefixRun : core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice AspisR1Stage2.Stage2Finish.E)) point ⟨2#usize⟩=ok alpha)
    (kr kout : verifier.Reader)
    (kappaRead : CheckpointBytes3Reader.readE kr=ok (.Ok kappa,kout))
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
  have hc := FJg_ReadSemanticCanon.native true bytes start stop semAlpha semanticRead
  have shape := FJr_AlphaPrefix.value point alpha bound prefixRun
  have halpha := FJr_AlphaPrefix.canonical point alpha bound cp prefixRun
  have ckappa := FJg_ReaderScalarCanon.e kr kout kappa kappaRead
  exact FJr_PairMeaning.value r semAlpha z w alpha f kappa out hc cz hw shape.2 len halpha ckappa run

#print axioms value
end AspisR1.FJr_ParsedPairMeaning
end
