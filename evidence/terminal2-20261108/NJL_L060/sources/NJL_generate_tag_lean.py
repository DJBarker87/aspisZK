from pathlib import Path
import json,sys
E=Path(__file__).resolve().parent;x=json.loads((E/'NJL_TAG_DATA.json').read_text());terms=x['terms'];offsets=x['offsets']
s='''import NJB_TagRaw
import NJB_Words
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJL_TagData
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
/-- Exact immutable payload checked natively against all272 terms/31 offsets.
There are no empty coordinates; spans1..54, at most4 products per chunk. -/
'''
s+='def offsets : Fin 31 → Nat := !['+','.join(map(str,offsets))+']\n'
s+='def blockList : List Nat := ['+','.join(str(t['block'])for t in terms)+']\n'
s+='def tagList : List U32 := ['+','.join(str(t['tag'])+'#u32'for t in terms)+']\n'
s+='''theorem block_length : blockList.length=272 := rfl
theorem tag_length : tagList.length=272 := rfl
theorem block_all : blockList.all (fun b=>decide (b<64))=true := by decide
theorem tag_all : tagList.all (fun t=>decide (t.val<2147483647))=true := by decide
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
 (List.ofFn (fun i : Fin 272=>i)).filter (fun i=>first c≤i.val ∧ i.val<last c)
theorem range (c : Fin 30) : (indices c).map Fin.val=List.range' (first c) (last c-first c) := by
 fin_cases c <;> decide
#print axioms block_length
#print axioms tag_length
#print axioms block_all
#print axioms tag_all
#print axioms tag_bound
#print axioms interval
#print axioms range
end AspisR1.NJL_TagData
end
'''
p=E/'NJL_TagData.lean'
if '--check'in sys.argv:assert p.read_text()==s
else:p.write_text(s)
