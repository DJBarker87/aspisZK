import NDO_JFu_Claims
import NDO_JFv_MainDecode
import NDO_JFu_Q26Source
set_option autoImplicit false
namespace AspisR1.JGe_Decode26
open Aeneas Aeneas.Std Result AspisR1PublicPreparation AspisS1ExtractedRoundChildren

theorem source : ∃ out,decodeMain 29#usize JFu_Q26Source.record 0#usize=ok (.Ok out) := by
  have canonical := PSem_FieldCanonical.source_payload 26#u8 JFw_NativeRow26.record JFw_NativeRow26.payload
    (by change 14≤26;omega) JFw_NativeRow26.accepted
  have shape : JFu_Q26Source.record.framed.length=933 := by
    simp only [JFu_Q26Source.record,JFw_NativeRow26.record,JFw_Frames.frame,Slice.length,List.length_cons]
    have size : JFw_NativeRow26.payload.val.length=928 := JFw_NativeRow26.payload_length
    omega
  exact JFv_MainDecode.success 29#usize JFu_Q26Source.record 0#usize
    (by change 14≤26;omega) (by rw [shape];change 5+32*(0+29)≤933;omega)
    (by rw [shape];omega) canonical
#print axioms source
end AspisR1.JGe_Decode26
