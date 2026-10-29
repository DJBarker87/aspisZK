from pathlib import Path
import subprocess,json,hashlib,shlex
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin54-20261029';rev=subprocess.check_output(['git','rev-parse','codex/cx-prover-rw-20261023'],text=True).strip()
def blob(p):return subprocess.check_output(['git','show',rev+':'+p])
native=json.loads(blob('evidence/pv-rj4idb-20261029/build-plan.json'));plan=json.loads((E/'build-plan.json').read_text());order=[]
def go(m):
 if m in order or m not in native['modules']:return
 for d in native['modules'][m]['imports']:go(d)
 order.append(m)
go('PV_RJ4IDB_OpenInputs')
accepted={}
for a in range(64600,64700):
 try:vs=json.loads(blob(f'evidence/pv-rj4idb-20261029/modules-{a}.json'))
 except subprocess.CalledProcessError:continue
 for v in vs:
  if v['accepted']:accepted[v['module']]=v
pins={}
for m in order:
 v=native['modules'][m];b=blob(v['path']);assert hashlib.sha256(b).hexdigest()==v['sha256'];assert accepted[m]['source_sha256']==v['sha256']
 pins[m]=dict(v,authority='h6 read-only audited pv-rj4idb object, candidate git-show source',candidate_revision=rev)
code=r'''import json,pathlib,hashlib,shutil,sys
x=json.load(sys.stdin);src=pathlib.Path('/home/dombarker/project-offloads/codex-pv-rj4idb-20261029');dst=pathlib.Path(x['workspace']);sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();checks=[]
for m in x['order']:
 v=x['records'][m];rel=m.replace('.','/');s=src/'sources'/(rel+'.lean');o=src/'objects'/(rel+'.olean');assert sha(s)==v['source_sha256'];assert sha(o)==v['object_sha256']
 for d,pin in v['dependencies'].items():
  dr=d.replace('.','/')+'.olean';q=next((p/dr for p in [dst/'objects',dst/'external'] if (p/dr).exists()),None);assert q and sha(q)==pin['sha256'],(m,d,str(q))
 ds=dst/'sources'/(rel+'.lean');do=dst/'objects'/(rel+'.olean');assert not ds.exists() and not do.exists();ds.parent.mkdir(parents=True,exist_ok=True);do.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(s,ds);shutil.copyfile(o,do)
 ir=src/'objects'/(rel+'.ir')
 if ir.exists():shutil.copyfile(ir,dst/'objects'/(rel+'.ir'))
 checks.append(dict(module=m,source_sha256=sha(s),object_sha256=sha(o),dependencies_checked=len(v['dependencies'])))
print(json.dumps(checks))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(dict(workspace=plan['workspace'],order=order,records={m:accepted[m] for m in order})),text=True,capture_output=True)
(E/'open-inputs-reuse.json').write_text(json.dumps(dict(candidate_revision=rev,exit=r.returncode,stdout=r.stdout,stderr=r.stderr,modules=pins,records={m:accepted[m] for m in order}),indent=2)+'\n');assert r.returncode==0,r.stderr
plan['modules'].update(pins);(E/'build-plan.json').write_text(json.dumps(plan,indent=2)+'\n')
# Runner uses the same plan for source/dependency hash enforcement.
r=subprocess.run(['ssh','dombarker@100.108.41.90','cat > '+shlex.quote(plan['workspace']+'/build-plan.json')],input=json.dumps(plan),text=True,capture_output=True);assert r.returncode==0,r.stderr
print('Reused',len(order),'audited source/object pairs; all imported object fingerprints match')
