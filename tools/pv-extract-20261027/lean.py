from pathlib import Path
import hashlib,json,re,shlex,subprocess,sys
root=Path(__file__).resolve().parents[2];ev=root/'evidence/pv-extract-20261027';n=int(sys.argv[1]);module=sys.argv[2];assert 42400<=n<=42699
p=root/'docs/research/v8-r0-zk-20261009/lean'/(module+'.lean');assert p.name.startswith('PV_Ext_')
tp=ev/'TALLY.json';t=json.loads(tp.read_text()) if tp.exists() else dict(lean_charged=0,kani=0,next_env_j_id=42400,attempts=[])
assert n==t['next_env_j_id'] and t['lean_charged']<60;t['next_env_j_id']=n+1;t['attempts'].append(dict(id=n,module=module));tp.write_text(json.dumps(t,indent=2)+'\n')
H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads';imports=re.findall(r'^import (\S+)',p.read_text(),re.M)
code='''from pathlib import Path
import json,hashlib
B=Path('/home/dombarker/project-offloads');e=json.loads((B/'r1-privacy-build-integration-20261019/env/J.json').read_text());r={}
for m in IMPORTS:
 for d in [str(B/'aspis-joint-20261019/objects')]+e['LEAN_PATH'].split(':'):
  p=Path(d)/(m.replace('.','/')+'.olean')
  if p.exists():r[m]=hashlib.sha256(p.read_bytes()).hexdigest();break
 else:raise SystemExit('missing object '+m)
print(json.dumps(r,sort_keys=True))
'''.replace('IMPORTS',repr(imports))
r=subprocess.run(['ssh',H,'python3','-'],input=code,text=True,capture_output=True)
if r.returncode:(ev/f'{n}-preflight-error.txt').write_text(r.stderr+r.stdout);raise SystemExit(r.stderr+r.stdout)
deps=json.loads(r.stdout);fp=hashlib.sha256(json.dumps(deps,sort_keys=True).encode()).hexdigest(); meta=dict(attempt=n,module=module,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),deps_fingerprint=fp,dependency_object_hashes=deps)
(ev/f'{n}-submission.json').write_text(json.dumps(meta,indent=2)+'\n');(ev/f'{n}-source.lean.txt').write_bytes(p.read_bytes())
subprocess.run(['scp',str(p),H+':'+B+'/aspis-joint-20261019/sources/'+module+'.lean'],check=True)
a=subprocess.run(['ssh',H,shlex.join([B+'/r1-privacy-build-integration-20261019/tools/run-joint.sh',str(n),module,'J','7000','8',fp])],text=True,capture_output=True);(ev/f'{n}-launcher.log').write_text(a.stdout+a.stderr); print(a.stdout+a.stderr)
if 'exit=' in a.stdout:
 t=json.loads(tp.read_text());t['lean_charged']+=1;t['attempts'][-1]['charged']=True;tp.write_text(json.dumps(t,indent=2)+'\n')
 raw=subprocess.check_output(['ssh',H,'cat '+B+'/aspis-fs-generic-20261006/evidence/out-'+str(n)+'.log'],text=True); timing=subprocess.check_output(['ssh',H,'cat '+B+'/aspis-fs-generic-20261006/evidence/time-'+str(n)+'.log'],text=True)
 (ev/f'{n}-out.log').write_text(raw);(ev/f'{n}-time.log').write_text(timing)
 meta.update(exit=int(re.search(r'exit=(\d+)',raw)[1]),axioms=[x for x in raw.splitlines() if 'depends on axioms' in x or 'does not depend on any axioms' in x],time_log=timing);(ev/f'{n}.json').write_text(json.dumps(meta,indent=2)+'\n')
else:print('UNCHARGED refusal; observe 180-second cooldown if reservation hold')
