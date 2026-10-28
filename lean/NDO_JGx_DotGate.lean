import NDO_JGx_DotMeaning
import NDO_JGv_WeightsExact
import NDO_JGx_DecodeInjective
import NDO_JGv_DotFields
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_DotGate
open Aeneas Aeneas.Std Result AspisR1Stage2

theorem source {C : Type} (err : C) (geometry : Port3_NativeGeometryBody.Ops C)
    (seed : Port3_NativeQueryBody.Ops) (a : verifier.Accumulator)
    (b : verifier.BatchedWeights) (flushed : Slice SAQ_WideABI.K)
    (updates : JFz_TX2_AccumulationChain.updates seed 12=ok (a,b))
    (flush : Port3_FlushInstall.flush b a.weights.deref=ok flushed)
    (size : flushed.val.length=64) (canonical : ∀ q∈flushed.val,Port3_FlushInstall.Canonical q) :
    SAG_DotClosed.source (JFw_Frames.window 8007 2048) flushed=ok (.Ok a.rhs) := by
  have scalars := JGv_QueryScalars.source err geometry seed a b updates
  have weights := JGv_WeightsExact.source err geometry seed a b flushed updates flush size canonical
  obtain ⟨dot,call⟩ := JGv_DotTotal.source (JFw_Frames.window 8007 2048) flushed size JGv_DotFields.source canonical
  have dotCanon := JGv_DotCanonical.source (JFw_Frames.window 8007 2048) flushed dot size JGv_DotFields.source canonical call
  have interpreted := JGx_DotMeaning.source dot (weights ▸ call)
  obtain ⟨_,_,cr,_,_,_,_⟩ := JGv_QueryRows.source err geometry seed 12 (by omega) a b updates
  have same := JGx_DecodeInjective.source dot a.rhs dotCanon cr (interpreted.trans (congrArg CheckpointBytes5Output.ofE scalars.1.symm))
  exact same ▸ call
#print axioms source
end AspisR1.JGx_DotGate
end
