import NDO_JFz_TX2_AccumulationChain
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_AccumulationFlush
open Aeneas Aeneas.Std Result AspisR1Stage2

theorem source {C : Type} (err : C) (geometrySeed : Port3_NativeGeometryBody.Ops C)
    (seed : Port3_NativeQueryBody.Ops) :
    ∃ a b flushed, JFz_TX2_AccumulationChain.updates seed 12=ok (a,b) ∧
      a.weights=JFo_Prepared.accumulator.weights ∧ a.next=22#usize ∧
      Port3_FlushInstall.flush b a.weights.deref=ok flushed ∧
      flushed.val.length=64 ∧ ∀ q∈flushed.val,Port3_FlushInstall.Canonical q := by
  obtain ⟨a,b,run,inv,next⟩ := JFz_TX2_AccumulationChain.twelve err geometrySeed seed
  obtain ⟨sum,history,phase⟩ := inv.2.2.2.2
  obtain ⟨flushed,flush,size,canon⟩ := JFn_Flush.source b phase.2.1
  exact ⟨a,b,flushed,run,inv.1,next,by rw [inv.1];exact flush,size,canon⟩
#print axioms source
end AspisR1.JFz_TX2_AccumulationFlush
end
