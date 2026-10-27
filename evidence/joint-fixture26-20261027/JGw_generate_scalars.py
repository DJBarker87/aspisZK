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
manifest=[];chunks={}
for i in range(10):
 for slot in range(4):
  off=10055+832*i+120*slot;bs=raw[off:off+104];ws=[int.from_bytes(bytes(bs[t:t+4]),'little') for t in range(0,104,4)];assert max(ws)<2147483647
  mod=f'JGw_Slot{i:02}_{slot}'
  s=f'''import JFr_TX2_ScalarRead
import JFr_TX2_DecodeCell
set_option autoImplicit false
noncomputable section
namespace AspisR1.{mod}
open Aeneas Aeneas.Std Result

def raw : Array U8 104#usize := ⟨{lit(bs)},by rfl⟩
def values : Array U32 26#usize := Array.make 26#usize [{','.join(f'{w}#u32' for w in ws)}]

theorem selected : ((JFr_TX2_Windows.array ⟨{i},by decide⟩).val.drop {120*slot}).take 104=raw.val := by
  rw [JFr_TX2_Windows.selected _ {120*slot} 104 (by decide)]
{select(off,104)}
'''
  for t,w in enumerate(ws):
   s+=f'''theorem decode{t:02} : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨{t},by decide⟩)=ok (some {w}#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change {w}<2147483647;omega)
#print axioms decode{t:02}
'''
  s+='''
theorem decode (t : Fin 26) : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw t)=
    ok (some (values.val[t.val]'(by rw [values.property];exact t.isLt))) := by
  fin_cases t
'''
  for t in range(26):s+=f'  · exact decode{t:02}\n'
  s+=f'''
theorem source (t : Fin 26) : JFr_TX2_ScalarRead.read (JFr_TX2_Windows.array ⟨{i},by decide⟩)
    {slot}#usize (Usize.ofNat t.val (by have := t.isLt;scalar_tac))=
      ok (values.val[t.val]'(by rw [values.property];exact t.isLt)) := by
  apply JFr_TX2_ScalarRead.source _ _ _ (by decide) (by exact t.isLt) (JFr_TX2_DecodeCell.cell raw t) _ _ (decode t)
  change ((JFr_TX2_Windows.array ⟨{i},by decide⟩).val.drop (120*{slot}+4*t.val)).take 4=_
  have h:=JFq_Range.nested (JFr_TX2_Windows.array ⟨{i},by decide⟩).val {120*slot} 104 (4*t.val) 4 (by have := t.isLt;omega)
  rw [←h,selected]
  rfl

#print axioms selected
#print axioms decode
#print axioms source
end AspisR1.{mod}
end
'''
  chunks.setdefault(i,[]).append(s)
  manifest.append(dict(module=mod,offset=off,count=104,sha256=hashlib.sha256(bytes(bs)).hexdigest(),source_sha256=hashlib.sha256(s.encode()).hexdigest()))
(P/'JGw_SLOT_WINDOWS.json').write_text(json.dumps(dict(proof_sha256=hashlib.sha256(bytes(raw)).hexdigest(),windows=manifest),indent=2)+'\n')

for i,parts in chunks.items():
 out=parts[0][:parts[0].index('set_option autoImplicit false')]+''.join(p[p.index('set_option autoImplicit false'):] for p in parts)
 f=R/f'lean/JGw_Scalars{i}.lean'
 if '--check' in sys.argv: assert f.read_text()==out,f
 else:f.write_text(out)
print('checked' if '--check' in sys.argv else 'generated','40 actual TX1 scalar slot read families')
