"""Retain the emitted metadata closure used by typed destructor bindings.
Unknown dedup keys remain unresolved. No byte image is introduced (D991).
"""
from pathlib import Path
import ast,hashlib,json,lzma,sys
E=Path('evidence/pv-lib-20261107/lane-A/session8');S=Path('evidence/pv-lib-20261107/lane-A/session5/thread-llbc.json.xz')
p=json.loads(lzma.decompress(S.read_bytes()))['translated'];dictionary={}
def collect(x):
 if isinstance(x,dict):
  if 'HashConsedValue'in x:
   i,v=x['HashConsedValue'];assert i not in dictionary or dictionary[i]==v;dictionary[i]=v
  for v in x.values():collect(v)
 elif isinstance(x,list):
  for v in x:collect(v)
collect(p);needed=set()
def visit(x):
 if isinstance(x,dict):
  if 'Deduplicated'in x:
   i=x['Deduplicated']
   if i not in needed:needed.add(i);visit(dictionary[i])
  for v in x.values():visit(v)
 elif isinstance(x,list):
  for v in x:visit(v)
fids=[248,504,608,157,405,486,584,661,683,644,454,4,602,762]
for i in fids:visit(p['fun_decls'][i])
# Include every call of ptr::drop_in_place and Cell::set plus its retained argument types.
def sites(x):
 if isinstance(x,dict):
  if 'Call'in x and isinstance(x['Call'],dict):
   c=x['Call']['call'];f=c['func']
   if f.get('Regular',{}).get('kind',{}).get('Fun',{}).get('Regular')in[248,504]:visit(c)
  for v in x.values():sites(v)
 elif isinstance(x,list):
  for v in x:sites(v)
sites(p)
ns={'json':json};src=Path('evidence/pv-lib-20261107/lane-A/session7/generate-intermediate-d685.py.txt').read_text();exec(compile(ast.Module(body=[n for n in ast.parse(src).body if isinstance(n,ast.FunctionDef)],type_ignores=[]),'helpers','exec'),ns)
rows=['  | '+str(i)+' => some ('+ns['data'](dictionary[i])+')' for i in sorted(needed)]
text='\n'.join(['import PV_LIB_A_CellSetBegin','set_option autoImplicit false','namespace PV_LIB_A_DropMetadata','open PV_STX2_Syntax','/- Exact hash-cons dictionary entries; unresolved keys are explicit. -/','def lookup : Nat → Option Data',*rows,'  | _ => none','#print axioms lookup','end PV_LIB_A_DropMetadata',''])
q=Path('lean/PV_LIB_A_DropMetadata.lean');m=dict(input=str(S),input_sha256=hashlib.sha256(S.read_bytes()).hexdigest(),functions=fids,keys=sorted(needed),source=str(q),source_sha256=hashlib.sha256(text.encode()).hexdigest(),allocation_images_defined=0)
if '--check'in sys.argv:assert q.read_text()==text;assert json.loads((E/'METADATA.json').read_text())==m
else:q.write_text(text);(E/'METADATA.json').write_text(json.dumps(m,indent=2)+'\n')
print(len(needed),'keys',len(text),'bytes')
