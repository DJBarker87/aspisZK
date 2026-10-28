import NDO_JHe_SdkParent
import NDO_JHe_WrapperReady
import NDO_JHg_World
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHk_WorldFirst
open Aeneas Aeneas.Std Result S2W_D189Entry S2W_D189Wrappers
open S2W_CommittedCheckpoint S2W_ReturnedCheckpoint S2W_WrapperLaws
attribute [local irreducible] JHb_Header.account JFx_NativeBytes.publicInput
  JFx_NativeBytes.proof JFx_NativeBytes.checkpoint

/-- The corrected TX2 support accounts do not change the three actual TX1
snapshots. This says nothing about equality of the whole heaps. -/
theorem accounts : JHg_World.e1.first=JHb_World.e1.first :=
  Eq.refl JHg_World.e1.first
#print axioms accounts

def post (saved : alloc.vec.Vec U8) :=
  writeBracket JHg_World.e1.heap 2 0 0 (source (nativeBytes saved))

/-- The existing child/SDK proof applied to the corrected world's snapshots,
then the wrapper constructor on THAT world's heap. -/
theorem source (base : AdapterRw.Ops) (stage : VTop_Stages.Ops)
    (saved : alloc.vec.Vec U8) (size : saved.val.length=1768)
    (child : AdapterRw.first_decoded (JHe_Natives.sdk base stage)
      (S6N_Getters.publicValue JGx_RealStatement.value) JFx_NativeBytes.publicInput
      JFx_NativeBytes.proof 10#usize=ok (.Ok saved)) :
    S2W_D189Wrappers.first (JHe_Natives.first base stage)
      CPH_FixtureData.copy CPH_FixtureData.allocator JHg_World.e1
      CPH_Program.verifier JHe_Natives.data1 ()=
        ok (.Ok (saved,post saved,())) := by
  have native : JHe_Natives.first base stage CPH_Program.verifier
      JHg_World.e1.first JHe_Natives.data1=ok (.Ok saved) := by
    rw [accounts]
    exact JHe_SdkParent.source base stage saved size child
  apply CPH_WrapperConstructor.first_success _ _ _ _ _ () () () saved
    (CPH_FixtureReserve.reserve_ok _) native rfl
  change (JHg_World.e1.buffers (JHg_World.e1.handles 2).1).val.length=
    (nativeBytes saved).length
  change (List.replicate 1768 (0#u8)).length=(nativeBytes saved).length
  rw [nativeBytes,List.length_map,size,List.length_replicate]
#print axioms source
end AspisR1.JHk_WorldFirst
end
