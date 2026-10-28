import NDO_JFv_TX2_GeometryReads
import NDO_JFs_TX2_GeometryPoints
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFv_TX2_GeometryFixture
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

def Calls {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) : Prop :=
  Port3_GeometryStage.geometry (JFv_TX2_GeometryOps.install err seed)
    JFo_Prepared.value.queries 10#usize 22#usize=ok (.Ok (JFv_TX2_Geometry.value err seed)) ∧
  JFv_TX2_GatherLoop.Meaning (JFv_TX2_Geometry.value err seed)

theorem calls {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) : Calls err seed :=
  ⟨JFv_TX2_Geometry.stage err seed,JFv_TX2_Geometry.meaning err seed⟩

theorem on_saved (saved : alloc.vec.Vec U8) (same : saved.val=JFx_NativeBytes.checkpoint.val)
    {Hash : Type} (H : Bytes → State) (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (realizes : JFn_HashBoundary.Realizes H) (querySeed : Port3_NativeQueryBody.Ops)
    {C : Type} (err : C) (geometrySeed : Port3_NativeGeometryBody.Ops C) :
    Port4A_ReaderInstall.reader true (JFn_HashBoundary.dictionary H D)
      (⟨saved.val,saved.property⟩ : Slice U8) JFx_NativeBytes.proof JFx_NativeBytes.publicInput .S2 hash=
      ok (.Ok (JFo_Prepared.value,JFo_Prepared.accumulator)) ∧
    JFs_TX2_Partial.Calls querySeed ∧ Calls err geometrySeed := by
  exact ⟨JFn_Resume.on_saved saved same H D hash realizes,JFs_TX2_Partial.calls querySeed,calls err geometrySeed⟩

theorem inhabited {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (background : Bytes → State) (querySeed : Port3_NativeQueryBody.Ops)
    {C : Type} (err : C) (geometrySeed : Port3_NativeGeometryBody.Ops C) :
    ∃ H : Bytes → State, JFn_HashBoundary.Realizes H ∧
      Port4A_ReaderInstall.reader true (JFn_HashBoundary.dictionary H D)
        JFx_NativeBytes.checkpoint JFx_NativeBytes.proof JFx_NativeBytes.publicInput .S2 hash=
        ok (.Ok (JFo_Prepared.value,JFo_Prepared.accumulator)) ∧
      JFs_TX2_Partial.Calls querySeed ∧ Calls err geometrySeed := by
  obtain ⟨H,realizes,reader,dots⟩ := JFs_TX2_Partial.inhabited D hash background querySeed
  exact ⟨H,realizes,reader,dots,calls err geometrySeed⟩
#print axioms calls
#print axioms on_saved
#print axioms inhabited
end AspisR1.JFv_TX2_GeometryFixture
end
