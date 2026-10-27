import XRz_RecordTransport
open Aeneas Aeneas.Std Result XRn_Join_Release XRo_Join_Carriers
set_option autoImplicit false
namespace XSc_RecordFieldCarriers
abbrev OQ := AspisR1PrefixAggregateParser.field.QM31
abbrev OW := AspisR1PrefixAggregateParser.field.wide_exact.WideExact

def q (x : OQ) : AspisR1PublicPreparation.aspis_core.field.QM31 :=
 ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def wide (x : OW) : XRn_Join_Wide := ⟨q x.c0,q x.c1⟩
/-- Exact old validator field-decoder carrier on all eight raw limbs. This is
an internal model transport, not another native P6 proof or caller restriction. -/
theorem limbs (a b c d e f g h : U32) :
 mapR (Option.map wide)
  (AspisR1PrefixAggregateParser.field.wide_exact.WideExact.from_limbs
   (Array.make 8#usize [a,b,c,d,e,f,g,h])) =
 aspis_core.field.wide_exact.WideExact.from_limbs
  (Array.make 8#usize [a,b,c,d,e,f,g,h]) := by
 unfold AspisR1PrefixAggregateParser.field.wide_exact.WideExact.from_limbs
  aspis_core.field.wide_exact.WideExact.from_limbs
  AspisR1PrefixAggregateParser.field.P
 simp only [Array.index_usize,Array.make,List.getElem?_cons_zero,List.getElem?_cons_succ,
  bind_tc_ok,List.all_cons,List.all_nil]
 split_ifs <;> simp_all [mapR,wide,q,XRn_Join_FieldExternal.oldQ,XRn_Join_q]
#print axioms limbs
end XSc_RecordFieldCarriers
