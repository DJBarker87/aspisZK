import NDO_JFz_TX2_GateFixture
import NDO_JFz_TX2_AccumulationFlush
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_UpdatesFixture
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

def Updates {C : Type} (_err : C) (_seed : Port3_NativeGeometryBody.Ops C)
    (querySeed : Port3_NativeQueryBody.Ops) : Prop :=
  ∃ a b flushed, JFz_TX2_AccumulationChain.updates querySeed 12=ok (a,b) ∧
    a.weights=JFo_Prepared.accumulator.weights ∧ a.next=22#usize ∧
    Port3_FlushInstall.flush b a.weights.deref=ok flushed ∧
    flushed.val.length=64 ∧ ∀ q∈flushed.val,Port3_FlushInstall.Canonical q

theorem on_saved (saved : alloc.vec.Vec U8) (same : saved.val=JFx_NativeBytes.checkpoint.val)
    {Hash : Type} (H : Bytes → State) (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (realizes : JFn_HashBoundary.Realizes H) (querySeed : Port3_NativeQueryBody.Ops)
    {C : Type} (err : C) (geometrySeed : Port3_NativeGeometryBody.Ops C) :
    Port4A_ReaderInstall.reader true (JFn_HashBoundary.dictionary H D)
      (⟨saved.val,saved.property⟩ : Slice U8) JFx_NativeBytes.proof JFx_NativeBytes.publicInput .S2 hash=
      ok (.Ok (JFo_Prepared.value,JFo_Prepared.accumulator)) ∧
    JFs_TX2_Partial.Calls querySeed ∧ JFz_TX2_GateFixture.Calls err geometrySeed ∧ Updates err geometrySeed querySeed := by
  obtain ⟨reader,dots,gates⟩ := JFz_TX2_GateFixture.on_saved saved same H D hash realizes querySeed err geometrySeed
  exact ⟨reader,dots,gates,JFz_TX2_AccumulationFlush.source err geometrySeed querySeed⟩

theorem inhabited {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (background : Bytes → State) (querySeed : Port3_NativeQueryBody.Ops)
    {C : Type} (err : C) (geometrySeed : Port3_NativeGeometryBody.Ops C) :
    ∃ H : Bytes → State, JFn_HashBoundary.Realizes H ∧
      Port4A_ReaderInstall.reader true (JFn_HashBoundary.dictionary H D)
        JFx_NativeBytes.checkpoint JFx_NativeBytes.proof JFx_NativeBytes.publicInput .S2 hash=
        ok (.Ok (JFo_Prepared.value,JFo_Prepared.accumulator)) ∧
      JFs_TX2_Partial.Calls querySeed ∧ JFz_TX2_GateFixture.Calls err geometrySeed ∧ Updates err geometrySeed querySeed := by
  obtain ⟨H,realizes,reader,dots,gates⟩ := JFz_TX2_GateFixture.inhabited D hash background querySeed err geometrySeed
  exact ⟨H,realizes,reader,dots,gates,JFz_TX2_AccumulationFlush.source err geometrySeed querySeed⟩
#print axioms on_saved
#print axioms inhabited
end AspisR1.JFz_TX2_UpdatesFixture
end
