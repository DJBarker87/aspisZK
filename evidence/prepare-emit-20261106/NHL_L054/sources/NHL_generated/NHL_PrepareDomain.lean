import NHL_PrefixPacket
import RPz7_S1WideViewSemanticV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHL_PrepareDomain
open Aeneas Aeneas.Std Result AspisR1CurrentCaller

/-- The OPEN verifier sees the SAME successful View from the complete CLOSED
prefix. Allocation success, semantic width, and byte identity are derived. -/
theorem reached (base : Ops) (reserved : Bool) {H : Type} (D : aspis_core.digest.Digest32 H)
 (proof : Slice U8) (v : verifier.View) (proofSize : proof.val.length=57607)
 (run : NHL_PrepareModel.Reaches base reserved D proof v) :
 reserved=true ∧ v.semantic.val.length=13831 ∧
 ∃ semantic y1 : Slice U8, semantic.val.length=13831 ∧ y1.val.length=928 ∧
 InstalledPreparation.sourceView proof semantic y1=ok (.Ok v) ∧ v.semantic=semantic := by
 cases reserved with
 | false =>
   have rejected := NHL_PrefixPacket.rejected base D proof
   change NHL_PrepareStages.buffers (NHL_Packets.installed base false) D proof=ok (.Ok v) at run
   rw [rejected] at run
   cases run
 | true =>
   obtain ⟨semantic,y1,semSize,ySize,prefix⟩ := NHL_PrefixPacket.accepted base D proof proofSize
   have view : InstalledPreparation.sourceView proof semantic y1=ok (.Ok v) := prefix.symm.trans run
   have same := InstalledPreparation.sourceView_semantic proof semantic y1 v view
   exact ⟨rfl,by rw [same];exact semSize,semantic,y1,semSize,ySize,view,same⟩
#print axioms reached
end AspisR1.NHL_PrepareDomain
