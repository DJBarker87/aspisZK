from pathlib import Path
import json,sys
E=Path(__file__).resolve().parent;x=json.loads((E/'NJL_TAG_DATA.json').read_text());terms=x['terms'];offsets=x['offsets'];outputs={}
for k in range(8):
 ts=terms[34*k:34*(k+1)];assert len(ts)==34;m=f'NJL_TagChunk{k:02}'
 s=f'''import NJB_TagRaw
set_option autoImplicit false
namespace AspisR1.{m}
open Aeneas Aeneas.Std
'''
 s+='def blocks : List Nat := ['+','.join(str(t['block'])for t in ts)+']\n'
 s+='def tags : List U32 := ['+','.join(str(t['tag'])+'#u32'for t in ts)+']\n'
 s+='''theorem block_length : blocks.length=34 := rfl
theorem tag_length : tags.length=34 := rfl
theorem block_all : blocks.all (fun b=>decide (b<64))=true := by decide
theorem tag_all : tags.all (fun t=>decide (t.val<2147483647))=true := by decide
#print axioms block_length
#print axioms tag_length
#print axioms block_all
#print axioms tag_all
'''+f'end AspisR1.{m}\n'
 outputs[m+'.lean']=s
s=''.join(f'import NJL_TagChunk{k:02}\n'for k in range(8))+'''import NJB_Words
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJL_TagData
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
/-- Exact272-term data split in34-cell chunks, each independently checked.
Named length/bound lemmas avoid reducing a272-deep generated literal. -/
'''
s+='def offsets : Fin 31 → Nat := !['+','.join(map(str,offsets))+']\n'
s+='def blockList : List Nat := '+' ++ '.join(f'NJL_TagChunk{k:02}.blocks'for k in range(8))+'\n'
s+='def tagList : List U32 := '+' ++ '.join(f'NJL_TagChunk{k:02}.tags'for k in range(8))+'\n'
s+='theorem block_length : blockList.length=272 := by\n simp only [blockList,List.length_append,'+','.join(f'NJL_TagChunk{k:02}.block_length'for k in range(8))+']\n'
s+='theorem tag_length : tagList.length=272 := by\n simp only [tagList,List.length_append,'+','.join(f'NJL_TagChunk{k:02}.tag_length'for k in range(8))+']\n'
s+='theorem block_all : blockList.all (fun b=>decide (b<64))=true := by\n simp only [blockList,List.all_append,'+','.join(f'NJL_TagChunk{k:02}.block_all'for k in range(8))+',Bool.and_self]\n'
s+='theorem tag_all : tagList.all (fun t=>decide (t.val<2147483647))=true := by\n simp only [tagList,List.all_append,'+','.join(f'NJL_TagChunk{k:02}.tag_all'for k in range(8))+',Bool.and_self]\n'
s+='''def block (i : Fin 272) : Fin 64 :=
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
   simp only [indices,List.getElem_map,List.getElem_ofFn,List.getElem_range',Nat.one_mul]
#print axioms block_length
#print axioms tag_length
#print axioms block_all
#print axioms tag_all
#print axioms tag_bound
#print axioms interval
#print axioms range_values
end AspisR1.NJL_TagData
end
'''
outputs['NJL_TagData.lean']=s
for n,s in outputs.items():
 p=E/n
 if '--check'in sys.argv:assert p.read_text()==s,n
 else:p.write_text(s)
