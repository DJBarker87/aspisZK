"""Generate tiny actual-emitted field fixtures; no new arithmetic model."""
from pathlib import Path
import json,random
E=Path(__file__).resolve().parent
ops=[('m_add','M31.add','word','xy'),('m_sub','M31.sub','word','xy'),('m_double','M31.double','word','x'),('reduce','reduce_u64','word','u'),('m_reduce','M31.reduce_u64','word','u'),('m_mul','M31.mul','word','xy'),('cm_add','CM31.add','cm','xy'),('cm_sub','CM31.sub','cm','xy'),('cm_mul','CM31.mul','cm','xy'),('cm_mul_m31','CM31.mul_m31','cm','xs'),('by_r','mul_by_r','cm','x'),('qm_add','QM31.add','qm','xy'),('qm_sub','QM31.sub','qm','xy'),('qm_mul','QM31.mul','qm','xy'),('qm_mul_m31','QM31.mul_m31','qm','xs'),('mul_u','wide_exact.mul_u','qm','x'),('wide_add','wide_exact.WideExact.add','wide','xy'),('wide_sub','wide_exact.WideExact.sub','wide','xy'),('wide_mul','wide_exact.WideExact.mul','wide','xy'),('wide_mul_m31','wide_exact.WideExact.mul_m31','wide','xs')]
P=2147483647;r=random.Random(11022026);cases=[]
for i in range(5):
 x=([0]*8 if i==0 else [P-1]*8 if i==1 else list(range(8)) if i==2 else [r.randrange(P) for _ in range(8)])
 y=([1]*8 if i==0 else [P-1]*8 if i==1 else list(range(8,16)) if i==2 else [r.randrange(P) for _ in range(8)])
 cases.append(dict(x=x,y=y,scalar=[0,P-1,17,743,123456789][i],u=[0,18446744073709551615,P,P*P,9223372036854775826][i]))
(E/'NEI_FIELD_FIXTURES.json').write_text(json.dumps(dict(ops=ops,cases=cases),indent=2)+'\n')
def word(n):return str(n)+'#u32'
def cm(v):return '⟨'+','.join(map(word,v[:2]))+'⟩'
def qm(v):return '⟨'+cm(v[:2])+','+cm(v[2:4])+'⟩'
def wide(v):return '⟨'+qm(v[:4])+','+qm(v[4:8])+'⟩'
mk={'word':lambda v:word(v[0]),'cm':cm,'qm':qm,'wide':wide}
pre='''import NEI_FieldWide
open Aeneas Aeneas.Std Result
namespace NEI_FieldFixtures
abbrev F := NEI_LineFull.aspis_core.field.M31
abbrev C := NEI_LineFull.aspis_core.field.CM31
abbrev Q := NEI_LineFull.aspis_core.field.QM31
abbrev W := NEI_LineFull.aspis_core.field.wide_exact.WideExact
def cmWords (x:C):List Nat := [x.a.val,x.b.val]
def qmWords (x:Q):List Nat := cmWords x.c0 ++ cmWords x.c1
def wideWords (x:W):List Nat := qmWords x.c0 ++ qmWords x.c1
def packed {T:Type} (r:Result T) (projection:T→List Nat):Lean.Json :=
 match r with
 | .ok x => Lean.toJson (projection x)
 | .fail _ => .str "fail"
 | .div => .str "div"
def fixtures : List (String × Lean.Json) := [
'''
lines=[]
for name,fn,kind,args in ops:
 for i,c in enumerate(cases):
  args=({'xy':mk[kind](c['x'])+' '+mk[kind](c['y']),'xs':mk[kind](c['x'])+' '+word(c['scalar']),'x':mk[kind](c['x']),'u':str(c['u'])+'#u64'})[args]
  proj={'word':'(fun x=>[x.val])','cm':'cmWords','qm':'qmWords','wide':'wideWords'}[kind]
  lines.append(' ("'+name+'/'+str(i)+'",packed (NEI_LineFull.aspis_core.field.'+fn+' '+args+') '+proj+')')
  args=next(o[3] for o in ops if o[0]==name)
(E/'NEI_FieldFixtures.lean').write_text(pre+',\n'.join(lines)+'\n]\n#eval (Lean.Json.mkObj fixtures).compress\nend NEI_FieldFixtures\n')
