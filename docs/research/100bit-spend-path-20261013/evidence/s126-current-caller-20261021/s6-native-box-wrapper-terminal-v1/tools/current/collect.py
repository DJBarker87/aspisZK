#!/usr/bin/env python3
"""Collect text/source only; reject live or incomplete native family scopes."""
from pathlib import Path
import hashlib,json,shlex,subprocess,sys,time
R=Path(__file__).resolve().parents[2];D=Path(__file__).parent
E=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021'
O=E/sys.argv[1];O.mkdir()
remote=r'''
from pathlib import Path
import json
B=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021')
files={};total=0;states={}
root_names={'nuc.py','plan.json','source-update.json','source-update-receipt.json','resource-review.json','update.py','review-high.py','run-families.py','admission-policy.json','family-sequence.jsonl'}
def add(p,rel):
 global total
 value=p.read_bytes();total+=len(value)
 assert len(value)<16*2**20 and total<128*2**20
 files[rel]=value.decode('utf-8')
for version in range(1,10):
 name='v'+str(version);w=B/('native-box-wrapper-20261026-'+name)
 if not w.exists():continue
 for p in w.iterdir():
  if p.is_file() and p.name in root_names:add(p,name+'/'+p.name)
 for case in ['positive','negative']+['family'+str(i) for i in range(25)]:
  a=w/('run-'+case)
  if not a.exists():continue
  if (a/'outer-terminal.json').exists():status='terminal'
  elif (a/'admission-before-scope.json').exists() and not json.loads((a/'admission-before-scope.json').read_text())['admitted']:status='admission_denied'
  else:raise RuntimeError('Live/incomplete scope: '+str(a))
  states[name+'/'+case]=status
  for p in a.iterdir():
   assert p.is_file() and p.suffix in {'.json','.log','.txt'},p
   add(p,name+'/'+case+'/'+p.name)
print(json.dumps({'files':files,'states':states,'bytes':total}))
'''
q=subprocess.run(['ssh','-o','BatchMode=yes','-o','ConnectTimeout=10','dombarker@100.108.41.90','python3 -I -S -B -c '+shlex.quote(remote)],capture_output=True,text=True)
assert q.returncode==0,q.stderr
result=json.loads(q.stdout)
for name,value in result['files'].items():
 target=O/name;target.parent.mkdir(parents=True,exist_ok=True);target.write_text(value)
local=Path('/private/tmp')
variants={'flat':'s126-native-box-wrapper-20261026-v2','families':'s126-native-box-wrapper-20261026-v3','chunks':'s126-native-box-wrapper-20261026-v4','field-cases':'s126-native-box-wrapper-20261026-v5'}
for label,directory in variants.items():
 w=local/directory
 for name in ['binding.json','registry-pins.json','Cargo.toml','Cargo.lock','harness/Cargo.toml','harness/src/lib.rs','sdk-reexport.rs']:
  dest=O/'proof-variants'/label/name;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes((w/name).read_bytes())
final=local/variants['field-cases'];binding=json.loads((final/'binding.json').read_text())
for name in binding['proof_only_arbitrary_derives']:
 dest=O/'native-source'/name;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes((final/name).read_bytes())
for source,label in [(local/'s126-native-box-wrapper-flat-tools-v1','flat'),(local/'s126-native-box-wrapper-family-tools-v1','families'),(local/'s126-native-box-wrapper-chunked-tools-v1','chunks'),(D,'current')]:
 for p in source.iterdir():
  if p.is_file() and p.suffix in ['.py','.rs']:
   dest=O/'tools'/label/p.name;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(p.read_bytes())
for name in ['s6-native-box-wrapper-local-v1','s6-native-box-wrapper-negative-local-v1']:
 w=E/name
 for p in w.iterdir():
  assert p.is_file() and p.suffix in ['.json','.log','.py'],p
  dest=O/'local'/name/p.name;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(p.read_bytes())
pins={str(p.relative_to(O)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(O.rglob('*')) if p.is_file()}
(O/'packet-pins.json').write_text(json.dumps({'schema':'focused-extractor-proof-packet-v1','files':pins,'remote_states':result['states'],'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'binary_files_included':False,'new_compiler_solver_calls':0,'collected_time':time.time()},indent=2)+'\n')
print(json.dumps({'packet':str(O.relative_to(R)),'files':len(pins),'remote_text_bytes':result['bytes']}))
