import RPu_FJi_DecodeQM31
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJi_DecodeUnwrap
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NQ)
theorem value (s : Slice U8) (o : Option NQ) (x : NQ)
    (decode : FIp_DotDecode.field.QM31.from_le_bytes s=ok o)
    (unwrap : core.option.Option.unwrap o=ok x) : FIo_QMValues.Canon x := by
  cases o with
  | none => cases unwrap
  | some y =>
    cases Result.ok.inj unwrap
    exact FJi_DecodeQM31.canonical s x decode
#print axioms value
end AspisR1.FJi_DecodeUnwrap
end
