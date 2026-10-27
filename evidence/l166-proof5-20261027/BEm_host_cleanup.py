"""Inspect only this job's scopes and remove only its known cargo target cache."""
from pathlib import Path
import hashlib,json,subprocess,shutil,time
B=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')
receipts=[]
for p in sorted(B.glob('BEm_*/receipt.json')):
 j=json.loads(p.read_text());j['receipt_mtime']=p.stat().st_mtime;receipts.append(j)
scopes=[]
for j in receipts:
 g=Path(j['cgroup']);populated=(g/'cgroup.events')
 text=populated.read_text() if populated.exists() else 'gone'
 assert 'populated 1' not in text,(j['attempt'],text)
 scopes.append({'attempt':j['attempt'],'cgroup':str(g),'status':text})
solver=[]
intervals=[(j['receipt_mtime']-j['wall_seconds']-5,j['receipt_mtime']+5,j['attempt']) for j in receipts if j['kind']=='kani']
for pattern in ['external-sat*.cnf','smt2_dec_problem*']:
 for p in Path('/tmp').glob(pattern):
  s=p.stat();overlaps=[a for lo,hi,a in intervals if lo<=s.st_mtime<=hi]
  solver.append({'path':str(p),'bytes':s.st_size,'mtime':s.st_mtime,'overlaps_own_kani_interval':overlaps,'action':'untouched; no source/process ownership attribution'})
tools={}
for p in [Path('/home/dombarker/.kani/kani-0.67.0/bin/cbmc'),Path('/home/dombarker/.kani/kani-0.67.0/bin/kani-compiler')]:
 tools[str(p)]={'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
versions={'scope':'No compiler/tool executable invoked during cleanup; static binary hashes only'}
target=B/'BEm_target'
assert target.parent==B and target.name=='BEm_target' and not target.is_symlink()
size=subprocess.check_output(['du','-sk',str(target)],text=True).strip() if target.exists() else 'absent'
if target.exists():shutil.rmtree(target)
print(json.dumps({'timestamp':time.time(),'scopes':scopes,'solver_temps':solver,'tool_pins':tools,'versions':versions,'removed_target':str(target),'removed_target_du_kib':size,'target_exists_after':target.exists(),'retained':'BEl Lean cache objects and source/receipts for lead reuse; no keys or foreign caches touched'},indent=2))
