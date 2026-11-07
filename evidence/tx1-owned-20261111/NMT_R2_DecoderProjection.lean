import NMT_R2_DecoderTotal
import NMT_R2_InputRoundtrip
import NMT_R2_ConcreteS1
set_option autoImplicit false
noncomputable section
namespace NMT_R2_DecoderProjection
open Aeneas Aeneas.Std NMT_345 RSL

/-- Exact Option transport on a reached statement-sized native input. No
success premise: both rejected and successful decoder Results are retained. -/
theorem decode_result (bytes : Slice U8) (length : bytes.val.length = 1880) :
 decodeCall bytes = .ok (NMT_R2_DecoderTotal.reply (NMT_R2_ConcreteS1.decode (bytes.val.map byte))) := by
 have mapped : (bytes.val.map byte).length = 1880 := by simpa using length
 unfold NMT_R2_ConcreteS1.decode
 rw [dif_pos mapped,NMT_R2_InputRoundtrip.from_native bytes length]
 obtain ⟨r,hr⟩ := NMT_R2_DecoderTotal.result bytes
 rw [hr]
 cases r <;> rfl
#print axioms decode_result
end NMT_R2_DecoderProjection
end
