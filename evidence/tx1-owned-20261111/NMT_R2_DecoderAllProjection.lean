import NMT_R2_DecoderProjection
import NMT_R2_DecodeWrongLength
set_option autoImplicit false
noncomputable section
namespace NMT_R2_DecoderAllProjection
open Aeneas Aeneas.Std NMT_345 RSL

/-- ALL native inputs, not only statement-sized or accepted inputs. -/
theorem source (bytes : Slice U8) : decodeCall bytes =
 .ok (NMT_R2_DecoderTotal.reply (NMT_R2_ConcreteS1.decode (bytes.val.map byte))) := by
 by_cases length : bytes.val.length = 1880
 · exact NMT_R2_DecoderProjection.decode_result bytes length
 · rw [NMT_R2_DecodeWrongLength.wrong_length bytes length]
   unfold NMT_R2_ConcreteS1.decode
   have bad : (bytes.val.map byte).length ≠ 1880 := by simpa using length
   rw [dif_neg bad]
   rfl
#print axioms source
end NMT_R2_DecoderAllProjection
end
