import NDO_JHb_Header
import RPz7_S6NativeAfterstateCodecV1
set_option autoImplicit false
namespace AspisR1.JHf_ScanCodec
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_terminal
attribute [local irreducible] JHb_Header.value

theorem encoded : encode_pool_v1_pair_verified_afterstate_v1 JFt_AfterstateValue.value=
    ok (.Ok JHb_Header.value) := by
  obtain ⟨bytes,contents,call⟩:=AspisS6NativeAfterstateCodec.accepted_inverse
    JHb_Header.value.to_slice JFt_AfterstateValue.value JHb_Header.candidate
  have same : bytes=JHb_Header.value := Subtype.ext contents
  exact same ▸ call
#print axioms encoded
end AspisR1.JHf_ScanCodec
