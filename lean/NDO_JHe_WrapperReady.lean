import NDO_JHe_Natives
import NDO_JHe_SdkReads
import RPz8_CPH_WrapperConstructor
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_WrapperReady
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_CommittedCheckpoint S2W_ReturnedCheckpoint S2W_WrapperLaws S2W_TrustedStd

def post (saved : alloc.vec.Vec U8) := writeBracket JHb_World.e1.heap 2 0 0 (source (nativeBytes saved))

theorem source (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) (saved : alloc.vec.Vec U8)
    (size : saved.val.length=1768)
    (native : JHe_Natives.first base stage CPH_Program.verifier JHb_World.e1.first JHe_Natives.data1=ok (.Ok saved)) :
    S2W_D189Wrappers.first (JHe_Natives.first base stage) CPH_FixtureData.copy CPH_FixtureData.allocator
      JHb_World.e1 CPH_Program.verifier JHe_Natives.data1 ()=ok (.Ok (saved,post saved,())) := by
  apply CPH_WrapperConstructor.first_success _ _ _ _ _ () () () saved
    (CPH_FixtureReserve.reserve_ok _) native rfl
  change (JHb_World.e1.buffers (JHb_World.e1.handles 2).1).val.length=(nativeBytes saved).length
  rw [JHe_SdkReads.checkpoint_buffer,nativeBytes,List.length_map,size]
  exact List.length_replicate
#print axioms source
end AspisR1.JHe_WrapperReady
end
