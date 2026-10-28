import NDO_JFv_View
import JGx_LibraryDecode
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_Inactive
open Aeneas Aeneas.Std Result
attribute [local irreducible] JFw_Frames.window JFx_NativeBytes.proof

theorem source : ∃ value,Port1_LibrarySource.decode (JFw_Frames.window 7495 32)=ok (some value) := by
  obtain ⟨out,read⟩ := JFv_View.inactive
  obtain ⟨parsed,call,same⟩ := PAln_InactiveDecode.parser _ _ read
  refine ⟨JGx_LibraryDecode.wide parsed,?_⟩
  rw [←JGx_LibraryDecode.decoder_agreement,call]
  rfl
#print axioms source
end AspisR1.JGx_Inactive
end
