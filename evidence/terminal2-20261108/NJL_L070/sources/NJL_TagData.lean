import NJL_TagChunk00
import NJL_TagChunk01
import NJL_TagChunk02
import NJL_TagChunk03
import NJL_TagChunk04
import NJL_TagChunk05
import NJL_TagChunk06
import NJL_TagChunk07
import NJB_Words
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJL_TagData
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
/-- Exact272-term data split in34-cell chunks, each independently checked.
Named length/bound lemmas avoid reducing a272-deep generated literal. -/
def offsets : Fin 31 → Nat := ![0,2,3,10,11,18,25,79,84,90,96,102,108,129,130,136,189,195,196,197,203,204,205,212,213,261,267,268,269,270,272]
def blockList : List Nat := NJL_TagChunk00.blocks ++ NJL_TagChunk01.blocks ++ NJL_TagChunk02.blocks ++ NJL_TagChunk03.blocks ++ NJL_TagChunk04.blocks ++ NJL_TagChunk05.blocks ++ NJL_TagChunk06.blocks ++ NJL_TagChunk07.blocks
def tagList : List U32 := NJL_TagChunk00.tags ++ NJL_TagChunk01.tags ++ NJL_TagChunk02.tags ++ NJL_TagChunk03.tags ++ NJL_TagChunk04.tags ++ NJL_TagChunk05.tags ++ NJL_TagChunk06.tags ++ NJL_TagChunk07.tags
theorem block_length : blockList.length=272 := by
 simp only [blockList,List.length_append,NJL_TagChunk00.block_length,NJL_TagChunk01.block_length,NJL_TagChunk02.block_length,NJL_TagChunk03.block_length,NJL_TagChunk04.block_length,NJL_TagChunk05.block_length,NJL_TagChunk06.block_length,NJL_TagChunk07.block_length]
theorem tag_length : tagList.length=272 := by
 simp only [tagList,List.length_append,NJL_TagChunk00.tag_length,NJL_TagChunk01.tag_length,NJL_TagChunk02.tag_length,NJL_TagChunk03.tag_length,NJL_TagChunk04.tag_length,NJL_TagChunk05.tag_length,NJL_TagChunk06.tag_length,NJL_TagChunk07.tag_length]
theorem block_all : blockList.all (fun b=>decide (b<64))=true := by
 simp only [blockList,List.all_append,NJL_TagChunk00.block_all,NJL_TagChunk01.block_all,NJL_TagChunk02.block_all,NJL_TagChunk03.block_all,NJL_TagChunk04.block_all,NJL_TagChunk05.block_all,NJL_TagChunk06.block_all,NJL_TagChunk07.block_all,Bool.and_self]
theorem tag_all : tagList.all (fun t=>decide (t.val<2147483647))=true := by
 simp only [tagList,List.all_append,NJL_TagChunk00.tag_all,NJL_TagChunk01.tag_all,NJL_TagChunk02.tag_all,NJL_TagChunk03.tag_all,NJL_TagChunk04.tag_all,NJL_TagChunk05.tag_all,NJL_TagChunk06.tag_all,NJL_TagChunk07.tag_all,Bool.and_self]
def block (i : Fin 272) : Fin 64 :=
 let b := blockList[i.val]'(by rw [block_length];exact i.isLt)
 ⟨b,of_decide_eq_true ((List.all_eq_true.mp block_all) b (List.getElem_mem _))⟩
def tag (i : Fin 272) : U32 := tagList[i.val]'(by rw [tag_length];exact i.isLt)
theorem tag_bound (i : Fin 272) : (tag i).val<2147483647 :=
 of_decide_eq_true ((List.all_eq_true.mp tag_all) (tag i) (List.getElem_mem _))
def first (c : Fin 30) : Nat := offsets c.castSucc
def last (c : Fin 30) : Nat := offsets c.succ
theorem interval (c : Fin 30) : first c<last c ∧ last c≤272 := by fin_cases c <;> decide
def indices (c : Fin 30) : List (Fin 272) :=
 List.ofFn (fun i : Fin (last c-first c)=>⟨first c+i.val,by have := (interval c).2;have := i.isLt;omega⟩)
/-- Generic contiguous interval identity, not a concrete272-cell filter replay. -/
theorem range_values (c : Fin 30) : (indices c).map Fin.val=List.range' (first c) (last c-first c) := by
 apply List.ext_getElem
 · simp only [indices,List.length_map,List.length_ofFn,List.length_range']
 · intro i hi hj
   simp only [indices,List.getElem_map,List.getElem_ofFn,List.getElem_range']
#print axioms block_length
#print axioms tag_length
#print axioms block_all
#print axioms tag_all
#print axioms tag_bound
#print axioms interval
#print axioms range_values
end AspisR1.NJL_TagData
end
