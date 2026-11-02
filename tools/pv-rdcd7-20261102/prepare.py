"""Use existing scope/run2 launchers in a new private proof workspace."""
from pathlib import Path
import subprocess,json,re,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd7-20261102';D='/home/dombarker/project-offloads/codex-pv-rdcd7-20261102';H='dombarker@100.108.41.90';G='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy'
plan={};order=[]
def go(m):
 if m in plan:return
 p=R/'docs/research/v8-r0-zk-20261009/lean'/(m.replace('.','/')+'.lean')
 if not p.exists():p=R/'docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023'/(m.split('.')[-1]+'.lean')
 b=p.read_bytes();deps=re.findall(r'^import\s+(\S+)',b.decode(),re.M)
 plan[m]=dict(path=str(p.relative_to(R)),sha256=hashlib.sha256(b).hexdigest(),imports=deps)
 for dep in deps:
  assert not dep.startswith('XR')
  if dep.startswith('R1Z.'):go(dep)
 order.append(m)
for m in ['R1Z.PV_RDCD5_ParserRange','R1Z.PV_RDCD5_V197','R1Z.PV_RDCD5_ParserFlat','R1Z.ProverRwSuccessParserSource','R1Z.PV_RDCD4_ParserWindows','R1Z.PV_RDCD4_V197']:go(m)
(E/'source-resolution.json').write_text(json.dumps(dict(modules=plan,compile_order=order),indent=2)+'\n')
# Read-only authority census: these are h5-owned modules, no higher pins.
for name in ['evidence/envj-rebuild-20261026/EJR_final-inventory.json','docs/research/100bit-spend-path-20261013/evidence/prover-commit47-20261022/final-source-freeze.json']:
 raw=subprocess.check_output(['git','show','research:'+name]);obj=json.loads(raw)
 def visit(x):
  if isinstance(x,dict):
   for k in ['module','name']:
    if isinstance(x.get(k),str):assert x[k].replace('/','.') not in plan,(name,x)
   for v in x.values():visit(v)
  elif isinstance(x,list):
   for v in x:visit(v)
 visit(obj)
r=subprocess.run(['ssh',H,f'mkdir -p {D}; python3 {G}/reservation.py {D}/upload-admission.json > {D}/upload-admission.log 2>&1'],capture_output=True,text=True)
for n in ['upload-admission.json','upload-admission.log']:
 q=subprocess.run(['ssh',H,f'cat {D}/{n}'],capture_output=True,text=True);assert q.returncode==0,q.stderr;(E/n).write_text(q.stdout)
a=json.load(open(E/'upload-admission.json'));assert r.returncode==0 and a.get('allowed') is True,(r.returncode,a)
manifest=subprocess.check_output(['git','show','research:evidence/pv-replay-20261027/receipts/external-object-manifest.json']);(E/'external-object-manifest.json').write_bytes(manifest)
subprocess.run(['ssh',H,f'mkdir -p {D}/lean-sources/R1Z {D}/lean-objects/R1Z'],check=True)
for p in [E/'external-object-manifest.json',E/'source-resolution.json',R/'tools/pv-rdcd7-20261102/preflight.py']:
 subprocess.run(['scp','-q',str(p),H+':'+D+'/'+p.name],check=True)
for m,x in plan.items():
 subprocess.run(['scp','-q',str(R/x['path']),H+':'+D+'/lean-sources/'+m.replace('.','/')+'.lean'],check=True)
print('Prepared',len(plan),'project modules; no objects reused and no compile launched')
