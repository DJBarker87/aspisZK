import NFO_PacketDecoder
set_option autoImplicit false
namespace NFO_PacketAccepted
open Aeneas Aeneas.Std Result

theorem accepted (bytes : List U8) (value : NFO_PacketDecoder.Output)
    (success : NFO_PacketDecoder.run bytes = ok (.Ok value)) :
    ∃ width : bytes.length = 792,
      NFO_RawDecode.decode (Array.to_slice (⟨bytes,width⟩ : Array U8 792#usize)) = ok (.Ok value) := by
  by_cases width : bytes.length = 792
  · exact ⟨width,(NFO_PacketDecoder.on_packet bytes width).symm.trans success⟩
  · simp only [NFO_PacketDecoder.run, dif_neg width] at success
    cases success
#print axioms accepted
end NFO_PacketAccepted
