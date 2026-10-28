import NDO_JFz_TX2_Gates
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_GateFixture
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

def Calls {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) : Prop :=
  JFv_TX2_GeometryFixture.Calls err seed ∧ (∀ i : Fin 12, FIp_CircleQuery.circle JFq_Alpha0.scalar (JFs_TX2_Dots.value i)
    (JFv_TX2_CircleGeometry.inverse err seed i)=ok (JFz_TX2_Gates.selected i)) ∧
  (∀ i : Fin 12, SAQ_LineQuery.line JFq_Alpha1.scalar (JFn_Values.value i)
    (JFv_TX2_CircleGeometry.inverse err seed i)=ok (JFz_TX2_Gates.lineValue i))

theorem on_saved (saved : alloc.vec.Vec U8) (same : saved.val=JFx_NativeBytes.checkpoint.val)
    {Hash : Type} (H : Bytes → State) (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (realizes : JFn_HashBoundary.Realizes H) (querySeed : Port3_NativeQueryBody.Ops)
    {C : Type} (err : C) (geometrySeed : Port3_NativeGeometryBody.Ops C) :
    Port4A_ReaderInstall.reader true (JFn_HashBoundary.dictionary H D)
      (⟨saved.val,saved.property⟩ : Slice U8) JFx_NativeBytes.proof JFx_NativeBytes.publicInput .S2 hash=
      ok (.Ok (JFo_Prepared.value,JFo_Prepared.accumulator)) ∧
    JFs_TX2_Partial.Calls querySeed ∧ Calls err geometrySeed := by
  obtain ⟨reader,dots,geometry⟩ := JFv_TX2_GeometryFixture.on_saved saved same H D hash realizes querySeed err geometrySeed
  exact ⟨reader,dots,geometry,JFz_TX2_Gates.circle err geometrySeed,JFz_TX2_Gates.line err geometrySeed⟩

theorem inhabited {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (background : Bytes → State) (querySeed : Port3_NativeQueryBody.Ops)
    {C : Type} (err : C) (geometrySeed : Port3_NativeGeometryBody.Ops C) :
    ∃ H : Bytes → State, JFn_HashBoundary.Realizes H ∧
      Port4A_ReaderInstall.reader true (JFn_HashBoundary.dictionary H D)
        JFx_NativeBytes.checkpoint JFx_NativeBytes.proof JFx_NativeBytes.publicInput .S2 hash=
        ok (.Ok (JFo_Prepared.value,JFo_Prepared.accumulator)) ∧
      JFs_TX2_Partial.Calls querySeed ∧ Calls err geometrySeed := by
  obtain ⟨H,realizes,reader,dots,geometry⟩ := JFv_TX2_GeometryFixture.inhabited D hash background querySeed err geometrySeed
  exact ⟨H,realizes,reader,dots,geometry,JFz_TX2_Gates.circle err geometrySeed,JFz_TX2_Gates.line err geometrySeed⟩
#print axioms on_saved
#print axioms inhabited
end AspisR1.JFz_TX2_GateFixture
end
