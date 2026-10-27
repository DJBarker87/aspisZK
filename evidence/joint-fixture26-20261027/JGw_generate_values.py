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
base='List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil'
manifest=[];chunks={}
for i in range(10):
 for j in range(4):
  off=10055+832*i+672+32*j;bs=raw[off:off+32];words=[int.from_bytes(bytes(bs[a:a+4]),'little') for a in range(0,32,4)]
  assert all(w<2147483647 for w in words)
  group=off//4096; assert (off+31)//4096==group
  mod=f'JGw_Value{i:02}_{j}'
  lengths=','.join(f'JFx_DataProof{k:02}.length' for k in range(15))
  small=','.join(f'JFx_DataProof{group:02}.c{k:02}_length' for k in cells[group])
  lit=','.join(f'{b}#u8' for b in bs)
  ws=','.join(f'{w}#u32' for w in words)
  s=f'''import JFn_ValueBlock
import JFo_QueryIndex
set_option autoImplicit false
noncomputable section
namespace AspisR1.{mod}
open Aeneas Aeneas.Std Result
open ExtractedRecordByteCanonicality ExtractedRecordLimbCanonicality

def bytes : List U8 := [{lit}]
def arr : Array U8 32#usize := ⟨bytes,by simp only [bytes,List.length_cons,List.length_nil];rfl⟩
def value : AspisR1RecordParser.field.wide_exact.WideExact := packed {" ".join(f"{w}#u32" for w in words)}

theorem selected : ((JFn_ValueBlock.value ⟨{i},by decide⟩).val.drop {32*j}).take 32=arr.val := by
  rw [JFn_ValueBlock.selected,JFq_Range.nested _ _ 128 {32*j} 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,{lengths},{base}]
  simp only [JFx_DataProof{group:02}.bytes,{small},{base}]
  rfl

'''
  for a,w in enumerate(words):s+=f'theorem word{a} : wordLE arr {a}={w}#u32 := rfl\n#print axioms word{a}\n'
  s+='\ntheorem decode : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes (Array.to_slice arr)=ok (some value) := by\n  apply (fixed_success_iff arr value).mpr\n  constructor\n  · intro n\n    fin_cases n\n'
  for a,w in enumerate(words):s+=f'    · change (wordLE arr {a}).val<2147483647\n      rw [word{a}]\n      change {w}<2147483647\n      omega\n'
  s+='  · simp only ['+','.join(f'word{a}' for a in range(8))+']\n    rfl\n'
  if j==0:
   query=[93499,147529,216823,245899,209371,192317,65593,183859,193093,159813,132355,218094,178080,149624,166165,42158,179622,21248,63860,55377,185637,14297][i]
   s+=f'\ntheorem query : Array.index_usize JFo_Prepared.value.queries {i}#usize=ok {query}#u32 :=\n  JFo_QueryIndex.source _ _ (by decide) {query}#u32 rfl\n#print axioms query\n'
  s+=f'''\ntheorem source : SAQ_Decoder.read (JFn_ValueBlock.value ⟨{i},by decide⟩) {j}#usize=
    ok (SAQ_RecordDecode.fromRecord value) :=
  JFn_FieldRead.source _ {j}#usize (by decide) (JFn_ValueBlock.length _) arr value selected decode

#print axioms selected
#print axioms decode
#print axioms source
end AspisR1.{mod}
end
'''
  f=R/f'lean/JGw_Values{i}.lean'
  chunks.setdefault(i,[]).append(s)
  manifest.append(dict(module=mod,offset=off,bytes_sha256=hashlib.sha256(bytes(bs)).hexdigest(),source_sha256=hashlib.sha256(s.encode()).hexdigest()))
(P/'JGw_QUERY_WINDOWS.json').write_text(json.dumps(dict(proof_sha256=hashlib.sha256(bytes(raw)).hexdigest(),windows=manifest),indent=2)+'\n')

for i,parts in chunks.items():
 head='import JFn_ArrayBuilder\n'
 body=''.join(p[p.index('set_option autoImplicit false'):] for p in parts)
 ns=f'JGw_Values{i}'
 body+=f"set_option autoImplicit false\nnoncomputable section\nnamespace AspisR1.{ns}\nopen Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody\n"
 body+='def value : Array SAQ_WideABI.E 4#usize := Array.make 4#usize ['+','.join(f'SAQ_RecordDecode.fromRecord JGw_Value{i:02}_{j}.value' for j in range(4))+']\n'
 body+=f"theorem source (seed : Port3_NativeQueryBody.Ops) :\n    (JFn_ArrayBuilder.ops seed).op0 4#usize\n      (verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact (JFn_ArrayBuilder.ops seed))\n      (JFo_Opening.value ⟨{i},by decide⟩)=ok value :=\n  JFn_ArrayBuilder.source seed ⟨{i},by decide⟩ _ _ _ _\n    "+' '.join(f'JGw_Value{i:02}_{j}.source' for j in range(4))+'\n#print axioms source\n'
 body+=f'end AspisR1.{ns}\nend\n'
 out=head+parts[0][:parts[0].index('set_option autoImplicit false')]+body
 f=R/f'lean/{ns}.lean'
 if '--check' in sys.argv: assert f.read_text()==out,f
 else:f.write_text(out)
print('checked' if '--check' in sys.argv else 'generated','ten actual TX1 ordered value-array source modules')
