import NNG_Total345
import NMT_R2_DecoderTotal
import LIBC_S1
import NMT_R2_DecodeWrongLength
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_DecoderGraph345
open Aeneas Aeneas.Std Result NMT_345

def reply : Option Statement → core.result.Result Statement PE
 | some st=>.Ok st | none=>.Err .InvalidAccountData

theorem bytes (b : Slice U8) : b.val.map NMT_345.byte=LIB_Carriers.bytes b := by
 apply List.map_congr_left
 intro x _
 apply UInt8.toNat_inj.mp
 exact NMT_345.byte_nat x
#print axioms bytes

/-- Complete native decoder result at the SAME snapshot bytes, matched to
the delivered S1 field on BOTH Option arms. No success or width premise. -/
theorem source (b : Slice U8) : decodeCall b=ok (reply (LIBC_S1.decode (LIB_Carriers.bytes b))) := by
 by_cases width : b.val.length=1880
 · have hostWidth : (LIB_Carriers.bytes b).length=1880 := by
    rw [NMS_R2N_RSLScalars.bytes_length];exact width
   unfold LIBC_S1.decode
   rw [dif_pos hostWidth,LIBC_Bytes.from_native]
   obtain ⟨r,run⟩ := NMT_R2_DecoderTotal.result b
   rw [run]
   cases r <;> rfl

 · rw [NMT_R2_DecodeWrongLength.wrong_length b width]
   unfold LIBC_S1.decode
   have hostWidth : (LIB_Carriers.bytes b).length≠1880 := by
    rw [NMS_R2N_RSLScalars.bytes_length];exact width
   rw [dif_neg hostWidth]
   rfl
#print axioms source
end AspisR1.NNG_DecoderGraph345
