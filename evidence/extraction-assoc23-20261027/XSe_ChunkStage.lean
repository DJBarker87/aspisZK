import XSe_ChunkPredicate
import XSe_ValidatorStage
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XSe_ChunkStage
/-- Full decoder/high-zero/error Result for each actual validator window. -/
theorem source (row : U8) (i : Usize) (s : Slice U8) (size : s.val.length=32) :
 XSe_ValidatorStage.kit row i s=
 ok (if XRn_Join_Bytes.validChunk 8 true s.val then .Ok () else .Err (.NonCanonical row i)) := by
 rw [XSe_ChunkPredicate.source s size]
 unfold XSe_ValidatorStage.kit
 rw [XSe_KitBytes.source s size]
 unfold _root_.aspis_core.field.wide_exact.WideExact.from_limbs XSe_ChunkPredicate.good
 by_cases canonical : ((XSe_OldBytes.words s).val.all (fun x => x<2147483647#u32))=true
 · rw [if_pos canonical,bind_tc_ok,canonical]
   simp only [Bool.true_and,XSe_OldBytes.words,Array.make,XRn_Join_FieldExternal.oldQ,
    XRn_Join_q,List.take_succ_cons,List.take_zero,List.drop_succ_cons,List.drop_zero,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,List.all_cons,
    List.all_nil,Bool.and_true]
   simp only [Bool.and_assoc]
   split_ifs <;> rfl
 · rw [if_neg canonical,bind_tc_ok]
   have hc : ((XSe_OldBytes.words s).val.all (fun x => x<2147483647#u32))=false :=
    Bool.eq_false_iff.mpr canonical
   rw [hc]
   rfl
#print axioms source
end XSe_ChunkStage
