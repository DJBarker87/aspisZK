import R1Z.PV_RDEAC_RoundValue
import R1Z.PV_RDEAC_NibbleModel
import R1Z.PV_RDEA_ActualEndpointConsumer
open Aeneas Aeneas.Std Result
namespace R1Z.PV_RDEAC_NameText
open PV_RDEAC_DigitText PV_RDEAC_ActualDigits PV_CBL_StringBytesAdapter

theorem digit_bytes (i : Fin 16) : encodeList (text i)=[PV_RDEA_NameBytes.digitByte i] := by
  fin_cases i <;> decide

def basenameText : List U8 → String
  | [] => ".burn"
  | b::bs => text (high b)++text (low b)++basenameText bs

theorem suffix_bytes : encodeList ".burn"=PV_RDEA_NameBytes.suffix := by decide

theorem name_bytes (bs : List U8) :
    encodeList (basenameText bs)=PV_RDEA_NameBytes.bytes (bs.map PV_RDEAC_NibbleModel.byte) := by
  induction bs with
  | nil => exact suffix_bytes
  | cons b bs ih =>
    simp only [basenameText,PV_RDEAC_AppendSimulation.encode_append,digit_bytes,
      List.map_cons,PV_RDEA_NameBytes.bytes,PV_RDEAC_NibbleModel.high,
      PV_RDEAC_NibbleModel.low,ih,List.cons_append,List.nil_append]

theorem name_length (bs : List U8) : (encodeList (basenameText bs)).length=2*bs.length+5 := by
  rw [name_bytes,PV_RDEA_NameBytes.byte_length,List.length_map]

#print axioms digit_bytes
#print axioms suffix_bytes
#print axioms name_bytes
#print axioms name_length
end R1Z.PV_RDEAC_NameText
