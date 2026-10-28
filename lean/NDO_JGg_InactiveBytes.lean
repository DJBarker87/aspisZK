import NDO_JGe_View
import RPz7_F3K_InactivePhysical
import NDO_JGg_Opening28
set_option autoImplicit false
namespace AspisR1.JGg_InactiveBytes
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation OriginalSerializerInstallation
open MultiproofConeCanonical OraclePortCompactDraft
attribute [local irreducible] JFx_NativeBytes.proof JFx_NativeBytes.proofBytes

theorem source (semantic y1 : Slice U8) (view : verifier.View)
    (accepted : sourceView JFx_NativeBytes.proof semantic y1=ok (.Ok view)) :
    sourceBytes (retainedView view).inactive=ok
      (Array.repeat 32#usize 0#u8) := by
  have serialized := sourceBytes_total (retainedView view).inactive
  have physical := F3K_InactivePhysical.bytes JFx_NativeBytes.proof semantic y1 view accepted _ serialized
  have zero : (JFw_Frames.window 7495 32).val=List.replicate 32 0#u8 := by
    have selected := JFz_Scan01.b00_selected
    have zeros : JFz_Scan01.b00=List.replicate 32 0#u8 := rfl
    simpa only [JFw_Frames.window] using selected.trans zeros
  have same : expectedBytes (retainedView view).inactive=Array.repeat 32#usize 0#u8 := by
    apply Subtype.ext
    apply MultiproofConeByteEquality.bytes_injective
    apply physical.trans
    simpa only [JFw_Frames.window,bytesOf,slice,List.map_take,List.map_drop,Array.repeat,show (32#usize).val=32 from rfl] using congrArg bytesOf zero
  exact same ▸ serialized
#print axioms source
end AspisR1.JGg_InactiveBytes
