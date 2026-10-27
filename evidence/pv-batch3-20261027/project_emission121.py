"""Link identical extracted dependencies; never replace a mismatching declaration."""
from pathlib import Path
import re,json,hashlib
D=Path(__file__).resolve().parent

def declarations(p,kind):
 s=p.read_text();out={}
 for block in re.split(r'\n(?=/--)',s):
  m=re.search(r'^('+kind+r')\s+(\S+)',block,re.M)
  if not m:continue
  body=block[m.start():];body=re.sub(r'\nend PV_B3_Copy_\d+\s*$','',body).strip()
  out[m.group(2)]=body
 return out
old=declarations(D/'generated-copy-117-08/Funs.lean','def');new=declarations(D/'generated-copy-121-03/Funs.lean','def')
oldtypes=declarations(D/'generated-copy-117-08/Types.lean','def|structure|inductive');newtypes=declarations(D/'generated-copy-121-03/Types.lean','def|structure|inductive')
shared=[];unique=[]
for n,b in newtypes.items():
 assert oldtypes.get(n)==b,('type mismatch',n)
 shared.append(dict(kind='type',name=n,body_sha256=hashlib.sha256(b.encode()).hexdigest()))
for n,b in new.items():
 if n in old:
  assert old[n]==b,('function mismatch',n)
  shared.append(dict(kind='function',name=n,body_sha256=hashlib.sha256(b.encode()).hexdigest()))
 else:unique.append((n,b))
s='''-- Projection of the unchanged raw121 emission, linked to byte-identical
-- extracted117 dependencies. See emission121-linkage.json and raw packets.
import PV_B3_Copy_117_Funs
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace PV_B3_Copy_117
'''
for n,b in unique:s+=re.sub(r'(\b\d+)#i32',r'\1#u32',b)+'\n\n'
s+=''.join('#print axioms '+n+'\n' for n,b in unique)+'end PV_B3_Copy_117\n'
p=D/'lean/PV_B3_PolynomialEmission.lean';p.write_text(s)
(D/'emission121-linkage.json').write_text(json.dumps(dict(shared=shared,new_declarations=[n for n,b in unique],projection_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),adapters=['Std/RustAttributes imports inherited from117','namespace121 linked to117 carrier','every reused declaration body identical, ignoring source/Rust metadata','positive shift literal type port only','generated options retained']),indent=2)+'\n')
print(len(shared),len(unique))
