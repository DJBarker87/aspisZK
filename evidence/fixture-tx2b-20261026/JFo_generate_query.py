from pathlib import Path
import re,sys,json,hashlib
R=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
parts=[]; cells=[]
for k in range(15):
 s=(R/f'lean/JFx_DataProof{k:02}.lean').read_text()
 cs=re.findall(r'def c(\d+) : List U8 := ([^\n]*)',s)
 data=[]
 for _,txt in cs:
  rep=re.fullmatch(r'List.replicate (\d+) (\d+)#u8',txt)
  data.extend([int(rep[2])]*int(rep[1]) if rep else [int(b) for b in re.findall(r'(\d+)#u8',txt)])
 parts.append(data)
 cells.append([int(n) for n,_ in cs])
raw=sum(parts,[]);assert len(raw)==57607
base='List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil'
manifest=[]
for i in range(10,22):
 for j in range(4):
  off=10055+832*i+32*j;bs=raw[off:off+32];words=[int.from_bytes(bytes(bs[a:a+4]),'little') for a in range(0,32,4)]
  assert all(w<2147483647 for w in words)
  group=off//4096; assert (off+31)//4096==group
  mod=f'JFo_Opening{i:02}_{j}'
  lengths=','.join(f'JFx_DataProof{k:02}.length' for k in range(15))
  small=','.join(f'JFx_DataProof{group:02}.c{k:02}_length' for k in cells[group])
  lit=','.join(f'{b}#u8' for b in bs)
  ws=','.join(f'{w}#u32' for w in words)
  s=f'''import JFo_QueryRead
import JFo_QueryIndex
set_option autoImplicit false
noncomputable section
namespace AspisR1.{mod}
open Aeneas Aeneas.Std Result
open ExtractedRecordByteCanonicality ExtractedRecordLimbCanonicality

def bytes : List U8 := [{lit}]
def arr : Array U8 32#usize := ⟨bytes,by simp only [bytes,List.length_cons,List.length_nil]⟩
def value : AspisR1RecordParser.field.wide_exact.WideExact := packed {" ".join(f"{w}#u32" for w in words)}

theorem selected : ((JFo_Opening.value ⟨{i},by decide⟩).val.drop {32*j}).take 32=arr.val := by
  rw [JFo_Opening.selected,JFq_Range.nested _ _ 832 {32*j} 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,{lengths},{base}]
  simp only [JFx_DataProof{group:02}.bytes,{small},{base}]
  rfl

'''
  for a,w in enumerate(words):s+=f'theorem word{a} : wordLE arr {a}={w}#u32 := rfl\n#print axioms word{a}\n'
  s+='\ntheorem decode : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes (Array.to_slice arr)=ok (some value) := by\n  apply (fixed_success_iff arr value).mpr\n  constructor\n  · intro n\n    fin_cases n <;> simp only ['+','.join(f'word{a}' for a in range(8))+'] <;> scalar_tac\n  · simp only ['+','.join(f'word{a}' for a in range(8))+']\n    rfl\n'
  if j==0:
   query=[93499,147529,216823,245899,209371,192317,65593,183859,193093,159813,132355,218094,178080,149624,166165,42158,179622,21248,63860,55377,185637,14297][i]
   s+=f'\ntheorem query : Array.index_usize JFo_Prepared.value.queries {i}#usize=ok {query}#u32 :=\n  JFo_QueryIndex.source _ _ (by decide) {query}#u32 rfl\n#print axioms query\n'
  s+=f'''\ntheorem source : SAQ_Decoder.read (JFo_Opening.value ⟨{i},by decide⟩) {j}#usize=
    ok (SAQ_RecordDecode.fromRecord value) :=
  JFo_QueryRead.source _ {j}#usize (by decide) (JFo_Opening.length _) arr value selected decode

#print axioms selected
#print axioms decode
#print axioms source
end AspisR1.{mod}
end
'''
  f=R/f'lean/{mod}.lean'
  if '--check' in sys.argv:assert f.read_text()==s,f
  else:f.write_text(s)
  manifest.append(dict(module=mod,offset=off,bytes_sha256=hashlib.sha256(bytes(bs)).hexdigest(),source_sha256=hashlib.sha256(s.encode()).hexdigest()))
(P/'JFo_QUERY_WINDOWS.json').write_text(json.dumps(dict(proof_sha256=hashlib.sha256(bytes(raw)).hexdigest(),windows=manifest),indent=2)+'\n')
