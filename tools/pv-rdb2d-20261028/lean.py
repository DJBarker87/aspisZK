"""Private one-module Env-J compile through the standing run2.py."""
from pathlib import Path
import subprocess,json,hashlib,re,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdb2d-20261028';D='/home/dombarker/project-offloads/codex-pv-rdb2c-20261028';H='dombarker@100.108.41.90'
n=int(sys.argv[1]);module=sys.argv[2];assert 61000<=n<=61099 and module.startswith(('R1Z/PV_RDB2D_','R1Z/PV_RDB2C_'))
assert n<61097 or any(x in module for x in ['Audit','Replay'])
p=R/'docs/research/v8-r0-zk-20261009/lean'/(module+'.lean');raw=p.read_bytes()
blob=subprocess.check_output(['git','rev-parse','HEAD:'+str(p.relative_to(R))],text=True).strip();assert subprocess.check_output(['git','show','HEAD:'+str(p.relative_to(R))])==raw
meta=dict(attempt=n,module=module,source_path=str(p.relative_to(R)),source_blob=blob,source_sha256=hashlib.sha256(raw).hexdigest(),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),authority='h5 git-tracked new module; all external manifest objects preflighted and selected prefixes checked',toolchain='Lean4.32.0 env-J',imports=re.findall(r'^import (\S+)',raw.decode(),re.M))
(E/f'{n}-submission.json').write_text(json.dumps(meta,indent=2)+'\n')
g='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy'
r=subprocess.run(['ssh',H,f'python3 {g}/reservation.py {D}/upload-{n}.json > {D}/upload-{n}.log 2>&1'],capture_output=True,text=True)
a=subprocess.check_output(['ssh',H,f'cat {D}/upload-{n}.json'],text=True);(E/f'{n}-upload-admission.json').write_text(a)
if r.returncode!=0 or json.loads(a).get('allowed') is not True:sys.exit(78)
subprocess.run(['scp','-q',str(p),H+':'+D+'/lean-sources/'+module+'.lean'],check=True)
cmd=['timeout','900','python3','/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence/run2.py',D+'/env-J.json',D+'/lean-objects',D+'/lean-sources',D+'/lean-objects/'+module+'.olean',D+'/lean-sources/'+module+'.lean','7000']
r=subprocess.run([sys.executable,str(R/'tools/pv-rdb2d-20261028/scope.py'),f'lean-{n}','focused Lean compilation',*cmd])
q=E/f'lean-{n}/receipt.json'
if q.exists():
 j=json.loads(q.read_text());j.update(meta);s=(q.parent/'output.log').read_text();j['print_axioms']=re.findall(r"'[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",s,re.S);q.write_text(json.dumps(j,indent=2)+'\n')
sys.exit(r.returncode)
