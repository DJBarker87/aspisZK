import NDO_JFz_TX2_ChainStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_AccumulationChain
open Aeneas Aeneas.Std Result AspisR1Stage2
abbrev updates := JFz_TX2_ChainStep.updates
abbrev Invariant := JFz_TX2_ChainStep.Invariant

theorem source {C : Type} (err : C) (geometrySeed : Port3_NativeGeometryBody.Ops C)
    (seed : Port3_NativeQueryBody.Ops) (n : Nat) (bound : n≤12) :
    ∃ a b,updates seed n=ok (a,b) ∧ Invariant n a b := by
  obtain ⟨out,run,inv⟩ := JFz_TX2_Sequence.source (JFz_TX2_ChainStep.transition seed)
    (JFo_Prepared.accumulator,JFo_Pending.value)
    (fun n state => JFz_TX2_ChainStep.Invariant n state.1 state.2) 12
    JFz_TX2_ChainStep.initial (JFz_TX2_ChainStep.source err geometrySeed seed) n bound
  exact ⟨out.1,out.2,run,inv⟩

theorem twelve {C : Type} (err : C) (geometrySeed : Port3_NativeGeometryBody.Ops C)
    (seed : Port3_NativeQueryBody.Ops) :
    ∃ a b,updates seed 12=ok (a,b) ∧ Invariant 12 a b ∧ a.next=22#usize := by
  obtain ⟨a,b,run,inv⟩ := source err geometrySeed seed 12 (by omega)
  exact ⟨a,b,run,inv,UScalar.eq_of_val_eq inv.2.1⟩
#print axioms source
#print axioms twelve
end AspisR1.JFz_TX2_AccumulationChain
end
