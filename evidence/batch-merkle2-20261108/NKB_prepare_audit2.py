"""Second completed full audit, only after newly merged NJZ-dependent source changes."""
from pathlib import Path
import sys,json,re,hashlib,lzma
sys.dont_write_bytecode=True
import NKB_resolve as R
E=Path(__file__).resolve().parent
names=['AUDIT.json','RAW_RESULTS.json','ROOT_STATEMENTS.md','AUDIT_ROOTS.json','AUDIT_MODULES.json','PROOF_INVENTORY.json','COMBINED_IMPORT.lean','EXPECTED_IMPORTS.jsonl','GATE_LOADED_scan.jsonl']
for n in names:
 b=R.read('NKB_'+n);p=E/('NKB_AUDIT1_'+n)
 if not p.exists() and not p.with_name(p.name+'.xz').exists():
  if len(b)>1000000:p.with_name(p.name+'.xz').write_bytes(lzma.compress(b,preset=6));p.with_name(p.name+'.sha256').write_text(hashlib.sha256(b).hexdigest()+'\n')
  else:p.write_bytes(b)
old=json.loads(R.read('NKB_AUDIT1_PROOF_INVENTORY.json'));modules=list(old['modules'])
new=['NKB_Canonical'+n for n in ['Range','Pair','Scalar','Echeck','Tail','ScalarLoop','Opening','SlotLoop','Geometry','Rows','RowsLoop','Constants','Prefix','Cuts','Domains','Congruence','ScalarBridge','KBridge']]
modules+=new
last={}
for line in (E/'NKB_ATTEMPTS.jsonl').read_text().splitlines():
 x=json.loads(line)
 if x['kind']=='lean':last[x['module']]=x
roots=['AspisR1.RPx_Deployed.deployed'];pins={}
for m in modules:
 p=E/'NKB_lean'/(m+'.lean');a=last[m];assert a['exit_status']==0,m
 assert R.read(a['attempt']+'/sources/NKB_lean/'+p.name)==p.read_bytes(),m
 ns=re.findall(r'^namespace (\S+)',p.read_text(),re.M)[0]
 for n in re.findall(r'^#print axioms (\S+)',p.read_text(),re.M):roots.append(n if n.startswith(ns+'.') else ns+'.'+n)
 pins[m]=dict(source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),successful_attempt=a['attempt'])
imports=['NJW_COMBINED_IMPORT','NJS_COMBINED_IMPORT','NJV_COMBINED_IMPORT','NJZ_COMBINED_IMPORT']+modules
s=''.join('import '+m+'\n' for m in imports)+'\nset_option pp.proofs false\n'+''.join('#print '+r+'\n#print axioms '+r+'\n' for r in roots)
(E/'NKB_COMBINED_IMPORT.lean').write_text(s);(E/'NKB_lean/NKB_COMBINED_IMPORT.lean').write_text(s)
expected={}
for blob in [R.read('NKB_AUDIT1_EXPECTED_IMPORTS.jsonl'),R.read('NKB_NJZ_EXPECTED_IMPORTS.jsonl')]:
 for line in blob.decode().splitlines():
  x=json.loads(line)
  if x['module'] in expected:assert expected[x['module']]==x['imports'],x['module']
  expected[x['module']]=x['imports']
for m in modules:expected[m]=['Init']+re.findall(r'^import (\S+)',(E/'NKB_lean'/(m+'.lean')).read_text(),re.M)
expected['NKB_COMBINED_IMPORT']=['Init']+imports
(E/'NKB_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=m,imports=v))+'\n' for m,v in sorted(expected.items())))
(E/'NKB_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=roots,groups=[roots]),indent=2)+'\n')
(E/'NKB_AUDIT_MODULES.json').write_text(json.dumps([['NKB_COMBINED_IMPORT']],indent=2)+'\n')
(E/'NKB_PROOF_INVENTORY.json').write_text(json.dumps(dict(modules=pins,roots=roots,target_established=False,closed_rows=0),indent=2)+'\n')
for old,num in [(48,99),(49,100),(50,101),(51,102)]:
 x=json.loads((E/f'NKB_L{old:03d}.json').read_text());x['attempt']=f'NKB_L{num:03d}';x['env']=json.loads((E/'NKB_ENV.json').read_text());x['expected_time']='Second and final complete audit after NJZ merge and new NKB canonical source proofs; same unchanged audit binary and hardened fixtures'
 (E/(x['attempt']+'.json')).write_text(json.dumps(x,indent=2)+'\n')
print(f'Audit2 prepared: {len(modules)} support modules / {len(roots)} roots / zero row closures')
