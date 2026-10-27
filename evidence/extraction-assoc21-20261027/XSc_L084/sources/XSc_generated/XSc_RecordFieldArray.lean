import XSc_RecordFieldStep
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XSc_RecordFieldArray
open XSc_RecordFieldStep XSc_RecordFieldTypes
def array (a b c d e f g h : U32) : Limbs := ⟨[a,b,c,d,e,f,g,h],rfl⟩
theorem source (a b c d e f g h : U32) :
 mapped (array a b c d e f g h)=
 _root_.aspis_core.field.wide_exact.WideExact.from_limbs (array a b c d e f g h) := by
 have r0 : Array.index_usize (array a b c d e f g h) 0#usize=ok a := rfl
 have r1 : Array.index_usize (array a b c d e f g h) 1#usize=ok b := rfl
 have r2 : Array.index_usize (array a b c d e f g h) 2#usize=ok c := rfl
 have r3 : Array.index_usize (array a b c d e f g h) 3#usize=ok d := rfl
 have r4 : Array.index_usize (array a b c d e f g h) 4#usize=ok e := rfl
 have r5 : Array.index_usize (array a b c d e f g h) 5#usize=ok f := rfl
 have r6 : Array.index_usize (array a b c d e f g h) 6#usize=ok g := rfl
 have r7 : Array.index_usize (array a b c d e f g h) 7#usize=ok h := rfl
 unfold mapped AspisR1PrefixAggregateParser.field.wide_exact.WideExact.from_limbs
 simp only [r0,r1,r2,r3,r4,r5,r6,r7,bind_tc_ok]
 unfold AspisR1PrefixAggregateParser.field.P
 unfold _root_.aspis_core.field.wide_exact.WideExact.from_limbs
 simp only [array,List.all_cons,List.all_nil]
 split_ifs <;> simp_all [XRo_Join_Carriers.mapR,wide,q,XRn_Join_FieldExternal.oldQ,XRn_Join_q]
#print axioms source
end XSc_RecordFieldArray
