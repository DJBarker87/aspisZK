"""Stage committed proof inputs only; existing launchers enforce every compile."""
from pathlib import Path
import subprocess,json,re,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd7-20261102';D='/home/dombarker/project-offloads/codex-pv-rdcd7-20261102';H='dombarker@100.108.41.90';G='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy'
plan={};order=[]
def go(m):
 if m in plan:return
 p=R/'docs/research/v8-r0-zk-20261009/lean'/(m.replace('.','/')+'.lean')
 if not p.exists():p=R/'docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023'/(m.split('.')[-1]+'.lean')
 b=p.read_bytes();assert b==subprocess.check_output(['git','show','HEAD:'+str(p.relative_to(R))],cwd=R)
 deps=re.findall(r'^import\s+(\S+)',b.decode(),re.M)
 plan[m]=dict(path=str(p.relative_to(R)),sha256=hashlib.sha256(b).hexdigest(),imports=deps,blob=subprocess.check_output(['git','rev-parse','HEAD:'+str(p.relative_to(R))],cwd=R,text=True).strip())
 for dep in deps:
  assert not dep.startswith('XR')
  if dep.startswith('R1Z.'):go(dep)
 order.append(m)
for m in ['R1Z.PV_RDCD5_V197Audit','R1Z.PV_RDCD5_NEPAudit','R1Z.PV_RDCD5_NEPDriver','R1Z.PV_RDCD5_V197Focused','R1Z.PV_RDCD5_V197FrozenManifest']:go(m)
kinds={m:('query-specification-only' if m=='R1Z.PV_RDCD5_V197Audit' else 'reserved-release' if m in ['R1Z.PV_RDCD5_V197Focused','R1Z.PV_RDCD5_V197FrozenManifest'] else 'ordinary-focused') for m in plan}
(E/'source-resolution.json').write_text(json.dumps(dict(modules=plan,compile_order=order,module_kinds=kinds),indent=2)+'\n')
r=subprocess.run(['ssh',H,f'python3 {G}/reservation.py {D}/stage-admission.json > {D}/stage-admission.log 2>&1'],capture_output=True,text=True)
for n in ['stage-admission.json','stage-admission.log']:
 q=subprocess.run(['ssh',H,f'cat {D}/{n}'],capture_output=True,text=True);assert q.returncode==0,q.stderr;(E/n).write_text(q.stdout)
a=json.load(open(E/'stage-admission.json'));(E/'stage').mkdir(exist_ok=True)
with (E/'stage/admission-history.jsonl').open('a') as log:log.write(json.dumps(dict(exit=r.returncode,admission=a))+'\n')
assert r.returncode==0 and a.get('allowed') is True,(r.returncode,a.get('allowed'),a.get('error'),'stage admission refusal; no upload')
for m,x in plan.items():subprocess.run(['scp','-q',str(R/x['path']),H+':'+D+'/lean-sources/'+m.replace('.','/')+'.lean'],check=True)
subprocess.run(['scp','-q',str(E/'source-resolution.json'),H+':'+D+'/source-resolution.json'],check=True)
q=subprocess.run(['ssh',H,f'cat {D}/preflight-result.json'],text=True,capture_output=True);assert q.returncode==0;qpath=E/'preflight-result.json';qpath.write_text(q.stdout)
print('Staged',len(plan),'committed project sources; no compile or library revalidation')
