import FJc_ByteCarrier
set_option autoImplicit false
namespace AspisR1.FJc_LimbParser
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NE)
open FJc_ByteCarrier (toRecord)
/-- The SAME eight limbs and ordered canonical guards in the two retained
source parser carriers, success-conditioned. -/
theorem source (limbs : Array U32 8#usize) (out : NE)
    (run : FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs limbs=ok (some out)) :
    AspisR1RecordParser.field.wide_exact.WideExact.from_limbs limbs=ok (some (toRecord out)) := by
  unfold FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs at run
  repeat' first
  | (solve | cases run)
  | uncase_result
  | head_reduce run
  | split at run
  all_goals
    have same := Option.some.inj (Result.ok.inj run)
    cases same
    simp_all [AspisR1RecordParser.field.wide_exact.WideExact.from_limbs,
      AspisR1RecordParser.field.P,FIo_Native.aspis_core.field.P,toRecord]
#print axioms source
end AspisR1.FJc_LimbParser
