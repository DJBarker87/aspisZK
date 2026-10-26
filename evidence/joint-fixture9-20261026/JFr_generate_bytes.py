"""Generate exact per-window native parser certificates, using the codec inverse.
Each cell is 16 bytes; fin_cases covers only Fin16, never the full buffer.
"""
from pathlib import Path
import re,json,sys
P=Path(__file__).resolve().parent;R=P.parents[1]
rows=json.loads((P/'JFr_coefficients.json').read_text())
for row in rows:
 r=row['round'];off=row['offset'];cs=row['coefficients'];m=f'JFr_Bytes{r:02}'
 scan=None
 for f in (R/'lean').glob('JFz_Scan*.lean'):
  if f'theorem selected : (JFx_NativeBytes.proof.val.drop {off}).take 448' in f.read_text():scan=f.stem;break
 assert scan
 s=f'''import JFr_Data{r:02}
import JFr_EncodedCell
import {scan}
set_option autoImplicit false
namespace AspisR1.{m}
open Aeneas Aeneas.Std Result RetainedFieldByteCodec
open AspisR1PublicPreparation
open AspisS1ExtractedRoundChildren
'''
 bs=[v for c in cs for w in c for v in w.to_bytes(4,'little')]
 s+=f'def raw : List U8 := {scan}.data\n'
 s+=f'theorem rawLength : raw.length=448 := {scan}.length\n#print axioms rawLength\n'
 s+=f'theorem selected : (JFx_NativeBytes.proof.val.drop {off}).take 448=raw := {scan}.selected\n#print axioms selected\n'
 for i,c in enumerate(cs):
  b=bs[16*i:16*i+16];cell=f'cell{i:02}';limbs=f'limbs{i:02}'
  s+=f'def {cell} : Array U8 16#usize := ⟨['+','.join(f'{v}#u8' for v in b)+'],by rfl⟩\n'
  s+=f'def {limbs} : QM31Limbs := !['+','.join(f'⟨{v},by change {v}<2147483647;omega⟩' for v in c)+']\n'
  prune=[f'{scan}.data']+[f'{scan}.j{k:02}' for k in range(13)]+[f'{scan}.b{k:02}_length' for k in range(14)]
  prune+=['List.drop_append','List.take_append','List.length_append','Nat.reduceAdd','Nat.reduceSub','Nat.reduceLeDiff','List.length_drop','List.drop_eq_nil_of_le','List.take_of_length_le','List.drop_zero','List.take_zero','List.nil_append','List.append_nil']
  s+=f'theorem rawCell{i:02} : (raw.drop {16*i}).take 16={cell}.val := by\n  simp only [raw,'+','.join(prune)+']\n  rfl\n#print axioms rawCell'+f'{i:02}\n'
  s+=f'''theorem encoded{i:02} : CandidateParserByteOrder.arrayBytes16 {cell}=encodeQM31LE {limbs} := by
  funext i
  fin_cases i <;> rfl
theorem parser{i:02} : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice {cell})=
    ok (some ⟨⟨{c[0]}#u32,{c[1]}#u32⟩,⟨{c[2]}#u32,{c[3]}#u32⟩⟩) :=
  JFr_EncodedCell.parser {cell} {limbs} encoded{i:02}
#print axioms encoded{i:02}
#print axioms parser{i:02}
'''
 s+=f'end AspisR1.{m}\n'
 f=R/'lean'/(m+'.lean')
 if '--check' in sys.argv:assert f.read_text()==s,m
 else:f.write_text(s)
print(json.dumps(dict(modules=10,checked='--check' in sys.argv,shape='Each native decode uses a named symbolic codec inverse on 16 bytes; no full-buffer evaluation.')))
