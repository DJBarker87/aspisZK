import RPu_FJl_QMArrayValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJl_QMSliceValue
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NQ qm)
/-- The byte length is supplied by the actual checked slice geometry. -/
theorem value (s : Slice U8) (q : NQ) (length : s.val.length=16)
    (run : FIp_DotDecode.field.QM31.from_le_bytes s=ok (some q)) :
    ExactLeafFieldCodec.decodeQM31 (MultiproofConeCanonical.bytesOf s.val)=some (decodeQM (qm q)) := by
  let a : Array U8 16#usize := ⟨s.val,length⟩
  exact FJl_QMArrayValue.value a q run
#print axioms value
end AspisR1.FJl_QMSliceValue
end
