from pathlib import Path
import subprocess,json,re,hashlib,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-relink-20261028';D='/home/dombarker/project-offloads/codex-pv-relink-20261028'
phase=sys.argv[1];assert phase in ['before-audit','after-replay']
sha=lambda b:hashlib.sha256(b).hexdigest()
res=json.loads((E/'source-resolution.json').read_text())['modules'];pre=json.loads((E/'preflight.json').read_text());ext=json.loads((E/'external-object-manifest.json').read_text());extmap={x['module'].replace('/','.'):x for x in ext}
for p in (R/'docs/research/v8-r0-zk-20261009/lean/R1Z').glob('PV_RL_*.lean'):
 s=subprocess.check_output(['git','show','HEAD:'+str(p.relative_to(R))],cwd=R);assert s==p.read_bytes()
 m='R1Z.'+p.stem;res[m]=dict(path=str(p.relative_to(R)),sha256=sha(s),blob=subprocess.check_output(['git','rev-parse','HEAD:'+str(p.relative_to(R))],cwd=R,text=True).strip(),revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),authority='h5 tracked own HEAD',imports=re.findall(r'^import (\S+)',s.decode(),re.M))
cone={}
def visit(m):
 if m in cone or m in extmap:return
 assert m in res,('unresolved closure module',m)
 cone[m]=res[m]
 assert not any(x.split('.')[-1].startswith('XR') for x in res[m]['imports'])
 for n in res[m]['imports']:visit(n)
visit('R1Z.PV_RL_ClosureReplay')
code=r'''
from pathlib import Path
import json,hashlib,time
D=Path(DIR);e=json.loads((D/'env-J.json').read_text());roots=[Path(x) for x in e['LEAN_PATH'].split(':')];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();errors=[];rows={}
for m,x in CONE.items():
 p=next((r/(m.replace('.','/')+'.olean') for r in roots if (r/(m.replace('.','/')+'.olean')).exists()),None)
 source=D/'lean-sources'/(m.replace('.','/')+'.lean') if m.startswith('R1Z.PV_RL_') else Path(PRE[m]['source_path'])
 if not source.exists() and m in ['R1Z.PV_RL_CombinedAudit','R1Z.PV_RL_ClosureReplay'] and PHASE=='before-audit':source_sha=None
 else:
  source_sha=sha(source) if source.exists() else None
  if source_sha!=x['sha256']:errors.append(['source',m,str(source),source_sha,x['sha256']])
 if p is None and not (PHASE=='before-audit' and m in ['R1Z.PV_RL_CombinedAudit','R1Z.PV_RL_ClosureReplay']):errors.append(['missing object',m])
 if p and m in PRE and PRE[m]['object_sha256'] and sha(p)!=PRE[m]['object_sha256']:errors.append(['changed imported object',m])
 rows[m]=dict(source_path=str(source),source_sha256=source_sha,object_path=str(p),object_sha256=sha(p) if p else None,source_authority=x)
ext=[]
for x in EXT:
 m=x['module'];p=next((r/(m+'.olean') for r in roots if (r/(m+'.olean')).exists()),None);h=sha(p) if p else None
 if h!=x['object_sha256']:errors.append(['external',m,str(p),h,x['object_sha256']])
 ext.append(dict(module=m,path=str(p),object_sha256=h))
fp=hashlib.sha256(json.dumps(dict(project={m:x['object_sha256'] for m,x in rows.items()},external=ext),sort_keys=True).encode()).hexdigest()
print(json.dumps(dict(ok=not errors,errors=errors,phase=PHASE,project=rows,external=ext,dependency_fingerprint=fp,toolchain=e['LEAN_GITHASH'],LEAN_PATH=e['LEAN_PATH'],checked_at=time.time())))
'''.replace('DIR',repr(D)).replace('CONE',repr(cone)).replace('PRE',repr(pre['project'])).replace('PHASE',repr(phase)).replace('EXT',repr(ext))
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
j=json.loads(r.stdout);(E/('closure-'+phase+'.json')).write_text(json.dumps(j,indent=2)+'\n');print(json.dumps(dict(ok=j['ok'],errors=j['errors'],project=len(cone),external=len(ext),fingerprint=j['dependency_fingerprint'])));raise SystemExit(not j['ok'])
