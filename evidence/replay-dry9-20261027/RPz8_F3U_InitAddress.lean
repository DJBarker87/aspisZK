import RPz8_F3U_InitCall
import RPz7_RawSourceGlobalOracleInitial
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3U_InitAddress
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisR1PublicPreparation AspisR1PublicPreparation.PreparedHashCode
open AspisR1PublicPreparation.SourceDigestAddresses

theorem head {H : Type} (D : aspis_core.Digest32 H) (hash : H)
    (pub : Slice U8) (root : Array U8 32#usize) (out : r1_wire.SemanticTranscript H)
    (success : erase (S1SemanticCode.newTranscript D hash pub root)=ok (.Ok out)) :
    ∃ state, RawK_Head.head (S1SemanticCode.newTranscript D hash pub root)=
      some (AspisR1.PublicInitFrame.frame (rawBytes pub) (decodeState root),state) := by
  obtain ⟨len,state,converted,first⟩ := F3U_InitCall.reached D hash pub root out success
  have address := SourceDigestAddresses.flatten_init pub root len
  change flatten (RawJ_DigestRead.initParts pub len root)=_ at address
  rw [SourceDigestAddresses.successful_length pub len converted] at address
  change flatten (RawJ_DigestRead.initParts pub len root)=
    AspisR1.PublicInitFrame.frame (rawBytes pub) (decodeState root) at address
  exact ⟨state,address ▸ first⟩

#print axioms head
end AspisR1.F3U_InitAddress
end
