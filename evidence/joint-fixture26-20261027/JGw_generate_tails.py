from pathlib import Path
import re,sys,json,hashlib
R=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
parts=[];cells=[]
for k in range(15):
 s=(R/f'lean/JFx_DataProof{k:02}.lean').read_text();cs=re.findall(r'def c(\d+) : List U8 := ([^\n]*)',s);data=[]
 for _,txt in cs:
  rep=re.fullmatch(r'List.replicate (\d+) (\d+)#u8',txt)
  data.extend([int(rep[2])]*int(rep[1]) if rep else [int(b) for b in re.findall(r'(\d+)#u8',txt)])
 parts.append(data);cells.append([int(n) for n,_ in cs])
raw=sum(parts,[]);assert len(raw)==57607
base='List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil'
lengths=','.join(f'JFx_DataProof{k:02}.length' for k in range(15))
def lit(bs):return '['+','.join(f'{b}#u8' for b in bs)+']'
def select(off,count):
 groups=range(off//4096,(off+count-1)//4096+1)
 small=','.join(x for g in groups for x in [f'JFx_DataProof{g:02}.bytes']+[f'JFx_DataProof{g:02}.c{k:02}_length' for k in cells[g]])
 return f'''  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,{lengths},{base}]
  simp only [{small},{base}]
  rfl
'''
manifest=[];collected={}
for i in range(10):
 for kind in range(3):
  mod=f'JGw_Tail{i:02}_{kind}'
  s=f'''import JFr_TX2_TailRead
set_option autoImplicit false
noncomputable section
namespace AspisR1.{mod}
open Aeneas Aeneas.Std Result
abbrev Q := JFr_TX2_TailRead.Q
'''
  for slot in range(4):
   start=120*slot+104 if kind==0 else 480+32*slot+16*(kind-1);off=10055+832*i+start;bs=raw[off:off+16]
   ws=[int.from_bytes(bytes(bs[t:t+4]),'little') for t in range(0,16,4)];assert max(ws)<2147483647
   a,b,c,d=(f'{w}#u32' for w in ws)
   s+=f'''
def bytes{slot} : Array U8 16#usize := ⟨{lit(bs)},by rfl⟩
def value{slot} : Q := ⟨⟨{a},{b}⟩,⟨{c},{d}⟩⟩
theorem selected{slot} : ((JFr_TX2_Windows.array ⟨{i},by decide⟩).val.drop {start}).take 16=bytes{slot}.val := by
  rw [JFr_TX2_Windows.selected _ {start} 16 (by decide)]
{select(off,16)}
theorem decode{slot} : FIp_DotDecode.field.QM31.from_le_bytes (Array.to_slice bytes{slot})=ok (some value{slot}) := by
  simp only [FIp_DotDecode.field.QM31.from_le_bytes,FIp_DotDecode.field.CM31.from_le_bytes,
    FIp_DotDecode.field.M31.from_le_bytes,FIp_DotDecode.field.P]
  rfl

theorem source{slot} : JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨{i},by decide⟩)
    {start}#usize {start+16}#usize=ok value{slot} :=
  JFr_TX2_TailRead.source _ _ _ (by rfl) (by decide) bytes{slot} value{slot} selected{slot} decode{slot}

#print axioms selected{slot}
#print axioms decode{slot}
#print axioms source{slot}
'''
   manifest.append(dict(module=f'JGw_Tails{i:02}',slot=slot,kind=kind,offset=off,count=16,sha256=hashlib.sha256(bytes(bs)).hexdigest()))
  s+=f'end AspisR1.{mod}\nend\n'
  collected[mod]=s
for i in range(10):
 name=f'JGw_Tails{i:02}'
 out=['import JFr_TX2_TailRead','set_option autoImplicit false','noncomputable section',f'namespace AspisR1.{name}','open Aeneas Aeneas.Std Result','abbrev Q := JFr_TX2_TailRead.Q']
 for k in range(3):
  text=collected[f'JGw_Tail{i:02}_{k}']
  text=text[text.index('\ndef bytes0'):text.index('\nend AspisR1.')]
  for word in ['bytes','value','selected','decode','source']:
   text=re.sub(r'\b'+word+r'([0-3])\b',lambda m:word+str(k)+'_'+m[1],text)
  out.append(text)
 out += [f'end AspisR1.{name}','end']
 text='\n'.join(out)+'\n';f=R/f'lean/{name}.lean'
 if '--check' in sys.argv:assert f.read_text()==text,f
 else:f.write_text(text)
(P/'JGw_TAIL_WINDOWS.json').write_text(json.dumps(dict(proof_sha256=hashlib.sha256(bytes(raw)).hexdigest(),windows=manifest),indent=2)+'\n')
