import NDO_JGc_TX2_QueryLoop
import NDO_JFz_TX2_UpdatesFixture
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGc_TX2_QueryFixture
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

def Calls {C : Type} (err : C) (geometrySeed : Port3_NativeGeometryBody.Ops C)
    (seed : Port3_NativeQueryBody.Ops) : Prop :=
  ∃ a b flushed,
    JFz_TX2_AccumulationChain.updates (JGc_TX2_QueryDictionary.input seed) 12=ok (a,b) ∧
    Port3_QueryStage.query (JFr_TX2_DotsBinding.ops seed)
      JFx_NativeBytes.proof JFo_Prepared.value JFo_Prepared.accumulator
      JFr_TX2_Powers.value none (JFv_TX2_Geometry.value err geometrySeed)
      JFo_Pending.value 22#usize=ok (.Ok (a,b)) ∧
    a.weights=JFo_Prepared.accumulator.weights ∧ a.next=22#usize ∧
    Port3_FlushInstall.flush b a.weights.deref=ok flushed ∧
    flushed.val.length=64 ∧ ∀ q∈flushed.val,Port3_FlushInstall.Canonical q

theorem on_saved (saved : alloc.vec.Vec U8) (same : saved.val=JFx_NativeBytes.checkpoint.val)
    {Hash : Type} (H : Bytes → State) (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (realizes : JFn_HashBoundary.Realizes H) (querySeed : Port3_NativeQueryBody.Ops)
    {C : Type} (err : C) (geometrySeed : Port3_NativeGeometryBody.Ops C) :
    Port4A_ReaderInstall.reader true (JFn_HashBoundary.dictionary H D)
      (⟨saved.val,saved.property⟩ : Slice U8) JFx_NativeBytes.proof JFx_NativeBytes.publicInput .S2 hash=
      ok (.Ok (JFo_Prepared.value,JFo_Prepared.accumulator)) ∧ Calls err geometrySeed querySeed :=
  ⟨JFn_Resume.on_saved saved same H D hash realizes,JGc_TX2_QueryLoop.source err geometrySeed querySeed⟩

theorem inhabited {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (background : Bytes → State) (querySeed : Port3_NativeQueryBody.Ops)
    {C : Type} (err : C) (geometrySeed : Port3_NativeGeometryBody.Ops C) :
    ∃ H : Bytes → State, JFn_HashBoundary.Realizes H ∧
      Port4A_ReaderInstall.reader true (JFn_HashBoundary.dictionary H D)
        JFx_NativeBytes.checkpoint JFx_NativeBytes.proof JFx_NativeBytes.publicInput .S2 hash=
        ok (.Ok (JFo_Prepared.value,JFo_Prepared.accumulator)) ∧ Calls err geometrySeed querySeed := by
  obtain ⟨H,realizes,reader,_⟩ := JFz_TX2_UpdatesFixture.inhabited D hash background querySeed err geometrySeed
  exact ⟨H,realizes,reader,JGc_TX2_QueryLoop.source err geometrySeed querySeed⟩
#print axioms on_saved
#print axioms inhabited
end AspisR1.JGc_TX2_QueryFixture
end
