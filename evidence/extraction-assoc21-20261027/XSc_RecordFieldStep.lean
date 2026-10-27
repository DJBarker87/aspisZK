import XSc_RecordFieldTypes
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XSc_RecordFieldStep
abbrev Limbs := Array U32 8#usize
abbrev Old := AspisR1PrefixAggregateParser.field.wide_exact.WideExact
def mapped (xs : Limbs) : Result (Option XRn_Join_Wide) :=
 XRo_Join_Carriers.mapR (fun x : Option Old => x.map XSc_RecordFieldTypes.wide)
  (AspisR1PrefixAggregateParser.field.wide_exact.WideExact.from_limbs xs)
/-- Split at the first actual decoder read; no whole eight-word normalization. -/
theorem rejected (xs : Limbs) (a : U32)
 (read : Array.index_usize xs 0#usize=ok a) (large : a≥2147483647#u32) :
 mapped xs=ok none := by
 unfold mapped AspisR1PrefixAggregateParser.field.wide_exact.WideExact.from_limbs
 rw [read,bind_tc_ok]
 unfold AspisR1PrefixAggregateParser.field.P
 rw [if_pos large]
 rfl
#print axioms rejected
end XSc_RecordFieldStep
