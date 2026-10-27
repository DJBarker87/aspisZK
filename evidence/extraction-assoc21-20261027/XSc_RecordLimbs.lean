import XSc_RecordFieldTypes
open Aeneas Aeneas.Std Result XRn_Join_Release XRo_Join_Carriers
set_option autoImplicit false
namespace XSc_RecordLimbs
open XSc_RecordFieldTypes
def array (a b c d e f g h : U32) : Array U32 8#usize := ⟨[a,b,c,d,e,f,g,h],rfl⟩
/-- The old validator's field carrier has exactly the kit's canonical-limb
branch on the same eight source words. No native leaf is re-proved. -/
theorem source (a b c d e f g h : U32) :
 mapR (Option.map wide)
  (AspisR1PrefixAggregateParser.field.wide_exact.WideExact.from_limbs (array a b c d e f g h)) =
 _root_.aspis_core.field.wide_exact.WideExact.from_limbs (array a b c d e f g h) := by
 unfold AspisR1PrefixAggregateParser.field.wide_exact.WideExact.from_limbs
  _root_.aspis_core.field.wide_exact.WideExact.from_limbs
  AspisR1PrefixAggregateParser.field.P
 simp only [Array.index_usize,array,List.getElem?_cons_zero,List.getElem?_cons_succ,
  bind_tc_ok,List.all_cons,List.all_nil]
 split_ifs <;> simp_all [mapR,wide,q,XRn_Join_FieldExternal.oldQ,XRn_Join_q]
#print axioms source
end XSc_RecordLimbs
