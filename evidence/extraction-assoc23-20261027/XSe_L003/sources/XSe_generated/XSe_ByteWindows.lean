import XSc_WordTransport
import XSc_RecordFieldGeneral
import XSc_RecordByteLength
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XSe_ByteWindows
def byte (s : Slice U8) (i : Nat) : U8 := s.val[i]?.getD 0#u8
theorem index (s : Slice U8) (i : Usize) (bound : i.val<s.val.length) :
 Slice.index_usize s i=ok (byte s i.val) := by
 obtain ⟨v,h,hv⟩ := WP.spec_imp_exists (Slice.index_usize_spec s i bound)
 rw [h,hv]
 simp only [byte,List.getElem?_eq_getElem bound,Option.getD_some]
theorem window (s : Slice U8) (i : Nat) (bound : i+3<s.val.length) :
 (s.val.drop i).take 4=[byte s i,byte s (i+1),byte s (i+2),byte s (i+3)] := by
 rw [List.drop_eq_getElem_cons (by omega : i<s.val.length),List.take_succ_cons,
  List.drop_eq_getElem_cons (by omega : i+1<s.val.length),List.take_succ_cons,
  List.drop_eq_getElem_cons (by omega : i+1+1<s.val.length),List.take_succ_cons,
  List.drop_eq_getElem_cons (by omega : i+1+1+1<s.val.length),List.take_succ_cons]
 simp only [List.take_zero,byte,List.getElem?_eq_getElem (by omega : i<s.val.length),
  List.getElem?_eq_getElem (by omega : i+1<s.val.length),
  List.getElem?_eq_getElem (by omega : i+2<s.val.length),
  List.getElem?_eq_getElem (by omega : i+3<s.val.length),Option.getD_some]
#print axioms index
#print axioms window
end XSe_ByteWindows
