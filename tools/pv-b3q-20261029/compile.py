"""One module per compliant scope, with cross-line failed-source guard."""
from pathlib import Path
import json,hashlib,re,sys,os
from run import H,run
B=H.parent/'codex-pv-b3p6-20261028';m=sys.argv[1];a=int(sys.argv[2]);assert m.startswith('PV_B3Q_')and 70200<=a<=70299
p=H/'lean'/(m+'.lean');srcsha=hashlib.sha256(p.read_bytes()).hexdigest()
assert not (H/f'lean-{a}'/'receipt/receipt.json').exists()
assert not json.loads((H/'preflight.json').read_text())['mismatches']
assert not json.loads((H/'cache-verification.json').read_text())['mismatches']
for base in [B,H]:
 for q in base.glob('lean-*/receipt/receipt.json'):
  r=json.loads(q.read_text())
  assert not(r.get('exit_status')!=0 and r.get('source_sha256')==srcsha),('unchanged failed proof/elaboration input',q,srcsha)
# Global ID collision check, including private directories.
for base,dirs,files in os.walk(H.parent):
 if Path(base)==H:dirs[:]=[];continue
 if len(Path(base).relative_to(H.parent).parts)>=5:dirs[:]=[]
 dirs[:]=[d for d in dirs if d not in {'target','sbf-target','charon-target','node_modules','.git','source','sources','.lake','objects','lean-objects','lean','generated','src','rebuild-objects'}]
 for name in dirs+files:assert not re.search(r'(?<![A-Za-z0-9])'+str(a)+r'(?![A-Za-z0-9])',name),('ID collision',base,name)
 for name in files:
  if name=='sent.txt':
   for line in (Path(base)/name).read_text().splitlines():
    f=line.split();assert not(len(f)>2 and f[2]==str(a)),('sent ID',base,line)
O=H/'lean-objects';S=H/'lean';env=json.loads((H/'env-J-private.json').read_text());search=[O]+[Path(x)for x in env['LEAN_PATH'].split(':')];deps={}
for imp in re.findall(r'^import (\S+)',p.read_text(),re.M):
 q=next((d/(imp.replace('.','/')+'.olean')for d in search if(d/(imp.replace('.','/')+'.olean')).exists()),None);assert q,imp
 deps[imp]=dict(path=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest())
cmd=['timeout','900','python3','/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence/run2.py',str(H/'env-J-private.json'),str(O),str(S),str(O/(m+'.olean')),str(p),'7000']
label=f'lean-{a}'
retry=0
while (H/label).exists():
 assert not (H/label/'receipt/receipt.json').exists(),'charged ID cannot be retried'
 retry+=1;label=f'lean-{a}-r{retry}'
status=run(label,cmd,'one focused Lean module; pinned run2.py, -M7000; inherited validated objects read-only')
R=H/label;(R/'source.lean').write_bytes(p.read_bytes())
if(R/'receipt/receipt.json').exists():
 q=R/'receipt/receipt.json';r=json.loads(q.read_text());r.update(module=m,attempt=a,source_sha256=srcsha,dependency_objects=deps,source_revision=(H/'revision').read_text().strip(),guard_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
 log=(R/'receipt/stdout.log').read_text()+'\n'+(R/'receipt/stderr.log').read_text();r['print_axioms']=re.findall(r"^.*(?:depends on axioms|does not depend on any axioms).*",log,re.M);q.write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(dict(module=m,attempt=a,exit=status,charged=(R/'receipt/receipt.json').exists())),flush=True);sys.exit(status)
