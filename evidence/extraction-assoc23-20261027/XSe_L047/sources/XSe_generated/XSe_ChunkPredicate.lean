import XSe_WordPredicates
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XSe_ChunkPredicate
open XSe_ByteWindows
def good (s : Slice U8) : Bool :=
 ((XSe_OldBytes.words s).val.all (fun x => x<2147483647#u32)) &&
 ((XSe_OldBytes.words s).val.drop 4).all (fun x => x==0#u32)
/-- Whole canonical/high-zero predicate on one arbitrary32-byte window. -/
theorem source (s : Slice U8) (size : s.val.length=32) :
 XRn_Join_Bytes.validChunk 8 true s.val=good s := by
 unfold XRn_Join_Bytes.validChunk good
 simp only [List.range_succ,List.range_zero,List.map_append,List.map_cons,List.map_nil,
  List.all_append,List.all_cons,List.all_nil,List.nil_append,List.cons_append,Nat.reduceMul,
  Bool.not_true,Bool.false_or,Nat.reduceLT,true_or,false_or,decide_true,Bool.and_true]
 rw [←XSe_WordPredicates.canonical s 0 (by omega)]
 rw [←XSe_WordPredicates.canonical s 4 (by omega)]
 rw [←XSe_WordPredicates.canonical s 8 (by omega)]
 rw [←XSe_WordPredicates.canonical s 12 (by omega)]
 rw [←XSe_WordPredicates.canonical s 16 (by omega)]
 rw [←XSe_WordPredicates.canonical s 20 (by omega)]
 rw [←XSe_WordPredicates.canonical s 24 (by omega)]
 rw [←XSe_WordPredicates.canonical s 28 (by omega)]
 rw [←XSe_WordPredicates.zero s 16 (by omega)]
 rw [←XSe_WordPredicates.zero s 20 (by omega)]
 rw [←XSe_WordPredicates.zero s 24 (by omega)]
 rw [←XSe_WordPredicates.zero s 28 (by omega)]
 simp only [window s 0 (by omega),
  window s 4 (by omega),
  window s 8 (by omega),
  window s 12 (by omega),
  window s 16 (by omega),
  window s 20 (by omega),
  window s 24 (by omega),
  window s 28 (by omega),XSe_OldBytes.words,Array.make,
 List.all_cons,List.all_nil,List.drop_succ_cons,List.drop_zero,Bool.and_true]
 have first : s.val.take 4=[byte s 0,byte s 1,byte s 2,byte s 3] := by
  simpa only [List.drop_zero] using window s 0 (by omega)
 simp only [first,Nat.reduceAdd]
 ac_rfl
#print axioms source
end XSe_ChunkPredicate
