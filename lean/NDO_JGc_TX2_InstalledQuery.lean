import NDO_JGc_TX2_QueryLoop
import RPz7_Tx2N_Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGc_TX2_InstalledQuery
open Aeneas Aeneas.Std Result

def raw (seed : Port3_NativeQueryBody.Ops) : Port3_NativeQueryBody.Ops :=
  SAQ_Decoder.install {seed with
    op20 := FIp_DotsAdapter.dots
    op17 := FIp_CircleQuery.circle
    widePartialEq := FIp_Equality.dictionary}

theorem dictionary (seed : Port3_NativeQueryBody.Ops) :
    Port4C_RowStd.install (Port5Q1_QueryPorts.install (raw seed))=JFr_TX2_DotsBinding.ops seed := rfl

theorem source (base : VTop_Stages.Ops) {C : Type} (err : C)
    (geometrySeed : Port3_NativeGeometryBody.Ops C) (seed : Port3_NativeQueryBody.Ops) :
    ∃ a b flushed,
      JFz_TX2_AccumulationChain.updates (JGc_TX2_QueryDictionary.input seed) 12=ok (a,b) ∧
      (Tx2N_Install.inner base true (raw seed)).op6
        JFx_NativeBytes.proof JFo_Prepared.value JFo_Prepared.accumulator
        JFr_TX2_Powers.value none (JFv_TX2_Geometry.value err geometrySeed)
        JFo_Pending.value 22#usize=ok (.Ok (a,b)) ∧
      a.weights=JFo_Prepared.accumulator.weights ∧ a.next=22#usize ∧
      (Tx2N_Install.inner base true (raw seed)).op9 b a.weights.deref=ok flushed ∧
      flushed.val.length=64 ∧ ∀ q∈flushed.val,Port3_FlushInstall.Canonical q := by
  obtain ⟨a,b,flushed,run,call,weights,next,flush,size,canon⟩ := JGc_TX2_QueryLoop.source err geometrySeed seed
  refine ⟨a,b,flushed,run,?_,weights,next,flush,size,canon⟩
  change Port3_QueryStage.query (Port4C_RowStd.install (Port5Q1_QueryPorts.install (raw seed)))
    _ _ _ _ _ _ _ _=_
  rw [dictionary]
  exact call
#print axioms dictionary
#print axioms source
end AspisR1.JGc_TX2_InstalledQuery
end
