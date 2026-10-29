"""Scripted Lean API/metadata port; shared selection declarations byte-checked."""
from pathlib import Path
import re,json,hashlib
D=Path('evidence/pv-b3p6-20261028');R=D/'raw227-complete-resume5';S=D/'raw227-select-resume5';record={}
sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
def blocks(s):return re.split(r'(?=^/-- \[)',s,flags=re.M)
def definition(b):
 m=re.search(r'^(?:def|structure|inductive) (\S+)',b,re.M)
 return m[1] if m else None
def body(b):
 m=re.search(r'^(?:def|structure|inductive) ',b,re.M);assert m
 return re.sub(r'\nend PV_B3P_227\s*$','',b[m.start():]).strip()
def normalized(s):return re.sub(r'\s+',' ',s).strip()
shared={}
for kind in ['Types','Funs']:
 old={definition(b):b for b in blocks((S/(kind+'.lean')).read_text())if definition(b)}
 raw=(R/(kind+'.lean')).read_text();out=[];reused=[]
 for b in blocks(raw):
  name=definition(b)
  if name in old:
   assert normalized(body(b))==normalized(body(old[name])),('shared declaration body differs',kind,name)
   reused.append(name)
   if b.rstrip().endswith('end PV_B3P_227'):out.append('\nend PV_B3P_227\n')
  else:out.append(b)
 p=''.join(out).replace('import Aeneas\n','import Aeneas.Std\nimport Aeneas.Tactic.RustAttributes\n')
 if kind=='Types':p=p.replace('import Aeneas.Std\n','import Aeneas.Std\nimport PV_B3P_SelectEmission227\n',1)
 else:p=p.replace('import PVB3P227ProjectedcolumnResume5.Types','import PV_B3P_CompleteTypes227')
 p=p.replace('discriminant isize, ','').replace('@[discriminant isize]\n','')
 numeric=[]
 for val in ['31','4']:
  n=p.count(val+'#i32')
  if n:p=p.replace(val+'#i32',val+'#u32');numeric.append(dict(value=int(val),count=n,change='positive shift argument tag i32 -> u32; value unchanged; separate value law required'))
 if kind=='Funs':
  before='Std.U64.wrapping_shr append_index link.weight_level'
  count=p.count(before); assert count==2
  p=p.replace(before,'Std.U64.wrapping_shr append_index (UScalar.cast .U32 link.weight_level)')
  numeric.append(dict(change='U8 dynamic shift argument widened to U32 for pinned Lean API',count=count,law='PV_B3P_Shift227.u8_u32_value'))
 assert not re.search(r'\b(sorry|admit|native_decide|implemented_by|axiom)\b',p)
 if kind=='Funs':
  names=re.findall(r'^def (\S+)',p,re.M);p+='\n'+''.join('#print axioms PV_B3P_227.'+n+'\n'for n in names)
 module='PV_B3P_CompleteTypes227' if kind=='Types' else 'PV_B3P_CompleteEmission227'
 ((D/'lean'/(module+'.lean')) if kind=='Types' else D/'ported227-complete-resume5.lean.txt').write_text(p)
 record[kind]=dict(raw_sha256=sha(raw),ported_sha256=sha(p),shared_declarations=reused,numeric_interface_ports=numeric)
record['edits']=['Aeneas.Std/RustAttributes imports','private module imports','reuse exactly body-identical Types/selection definitions from focused extraction','remove unsupported discriminant metadata, constructor order/payloads unchanged','positive shift argument interface tags; numeric value laws required','append axioms queries']
record['raw_emission_modified']=False
(D/'port227-complete-resume5.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:v['shared_declarations']for k,v in record.items()if isinstance(v,dict)}))
