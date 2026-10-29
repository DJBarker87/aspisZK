"""One unchanged-source rebuild or focused statement check; no source repair."""
from pathlib import Path
import json,hashlib,subprocess,sys,os,re,time
D=Path('/home/dombarker/project-offloads/codex-pv-mfd-20261029'); B=D.parent/'codex-pv-b3p6-20261028'; OLD=D.parent/'codex-pv-mfb-20261029'
PREV=D.parent/'codex-pv-mfc-20261029'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
f=json.load(open(OLD/'dlib-preflight-input.json')); inp=json.load(open(D/'rebuild-input.json'));mods=inp['modules']; env=f['environment']; roots=[Path(x) for x in env['LEAN_PATH'].split(':')]
mode,m,n=sys.argv[1:];n=int(n);assert 70000<=n<=70099
O=D/f'lean-{n}';assert not (O/'result.json').exists();O.mkdir(exist_ok=True)
# Guard all elaboration failures in this line. Prior pre-elaboration failures may
# be retried only with an explicit environment-correction receipt.
if mode=='check':
 cs=inp['rows'][m];text='import '+cs['module']+'\n#check '+cs['theorem']+'\n#print axioms '+cs['theorem']+'\n';module='PV_MF_'+m;p=D/'sources'/(module+'.lean');p.write_text(text)
else:module=m;p=D/'sources'/(m.replace('.','/')+'.lean');assert sha(p)==mods[m]['sha256']
ss=sha(p)
for q in list(PREV.glob('lean-*/result.json'))+list(D.glob('lean-*/result.json')):
 j=json.load(open(q));assert not(j.get('elaboration_failed') and j['source_sha256']==ss),('unchanged failed source',q)
prior=[]
if mode=='rebuild':
 for q in B.glob('lean-*/receipt/receipt.json'):
  j=json.load(open(q))
  if j.get('exit_status',0)!=0 and j.get('source_sha256')==ss:
   log=''.join(t.read_text(errors='replace') for t in [q.parent/'stdout.log',q.parent/'stderr.log'] if t.exists())
   environmental=bool(re.search(r"object file .* does not exist|unknown module prefix|failed to write|no such file|No such file|cannot find",log,re.I))
   assert environmental,('previous same-source proof/elaboration failure',str(q),log[-2000:])
   prior.append(dict(receipt=str(q),class_='before elaboration: dependency/object/output staging',environment_correction='all imports now preflighted and private output parent created',log=log[-2000:]))
# Verify every external h4 object before first import (cached verified manifest
# is never used as a substitute for current disk hashing).
ext=json.load(open(OLD/'external-object-manifest.json')); extmap={v['module'].replace('.','/'):v for v in ext}
for v in ext:
 key=v['module'].replace('.','/');p0=next((r/(key+'.olean') for r in roots if (r/(key+'.olean')).exists()),None)
 assert p0 and sha(p0)==v['object_sha256'],('h4',key,str(p0))
seen={}
def base_visit(k):
 k=k.replace('.','/')
 if k in seen:return
 j=f['source_closure'].get(k) or dict(external=True,object_sha256=extmap[k]['object_sha256']);p0=next((r/(k+'.olean') for r in roots if (r/(k+'.olean')).exists()),None);assert p0,k
 if j.get('external'):assert sha(p0)==j['object_sha256'];seen[k]=dict(external=True,path=str(p0),sha256=sha(p0));return
 rec=f['project'][k];assert str(p0)==rec['object_path'] and sha(p0)==rec['object_sha256'],k
 sp=D.parent/'codex-pv-dlib-20261028/lean-sources'/(k+'.lean');assert sha(sp)==j['source_sha256']==j['head_sha256']
 seen[k]=dict(source=j,object_path=str(p0),object_sha256=sha(p0))
 for dep in j['imports']:base_visit(dep)
 if k.startswith('R1Z/'):
  companion=D/'objects'/(k+'.olean');companion.parent.mkdir(parents=True,exist_ok=True)
  if not companion.exists():companion.symlink_to(p0)
  assert sha(companion)==rec['object_sha256']
# Only needed pinned project closure; source-to-object and transitive hashes.
base_visit('R1Z.ProverRwFullExternalFuns')
obj=D/'objects';obj.mkdir(exist_ok=True)
own={}
def visit(k):
 if k not in mods:base_visit(k);return
 if k in own:return
 q=obj/(k.replace('.','/')+'.olean');assert q.exists(),('missing predecessor',k)
 receipts=[json.load(open(z)) for root in [PREV,D] for z in root.glob('lean-*/result.json')]
 rec=next(z for z in receipts if z.get('module')==k and z['exit']==0 and z.get('mode')=='rebuild')
 assert sha(q)==rec['object_sha256'] and sha(D/'sources'/(k.replace('.','/')+'.lean'))==mods[k]['sha256'],k
 # Reused objects retain a complete dependency fingerprint, checked recursively.
 if rec['attempt']<70000:
  oldpre=json.load(open(PREV/f"lean-{rec['attempt']}/preflight.json"))
  assert oldpre['environment']==env
  for ik,iv in oldpre['private_imports'].items():
   iq=obj/(ik.replace('.','/')+'.olean');assert iq.exists() and sha(iq)==iv['object_sha256'],('reused dependency mismatch',k,ik)
 own[k]=dict(source_sha256=mods[k]['sha256'],object_sha256=sha(q),path=str(q),attempt=rec['attempt'])
 for dep in mods[k]['imports']:visit(dep)
imports=([inp['rows'][m]['module']] if mode=='check' else mods[m]['imports'])
for dep in imports:visit(dep)
out=obj/(module.replace('.','/')+'.olean');out.parent.mkdir(parents=True,exist_ok=True)
pre=dict(source_revision=inp['source_revision'],module=module,mode=mode,source_sha256=ss,external_objects_checked=len(ext),external_manifest_sha256=sha(OLD/'external-object-manifest.json'),base_project=seen,private_imports=own,toolchain=env['LEAN_GITHASH'],environment=env,previous_environment_failures=prior)
(O/'preflight.json').write_text(json.dumps(pre,indent=2)+'\n')
cd=D/'cooldown.json'
if cd.exists() and time.time()<json.load(open(cd))['until']:sys.exit(78)
G=D.parent/'codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy'
with (O/'admission.log').open('w') as log:a=subprocess.run(['python3',str(G/'reservation.py'),str(O/'admission.json')],stdout=log,stderr=subprocess.STDOUT)
if a.returncode or json.load(open(O/'admission.json')).get('allowed') is not True:
 cd.write_text(json.dumps(dict(until=time.time()+180)));sys.exit(78)
# Stable same-cohort prefix; run2 prepends only this job's private output dir.
ep=D/'env-J.json';ep.write_text(json.dumps(env));cmd=['timeout','900','python3',str(D.parent/'aspis-fs-generic-20261006/evidence/run2.py'),str(ep),str(obj),str(D/'sources'),str(out),str(p),'7000']
launch=['systemd-run','--user','--scope','--unit=pv-mfd-lean-'+str(n),'-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(G/'barrier.py'),str(O/'barrier.json'),'python3',str(B/'capped.py'),str(O/'receipt'),'focused unchanged pinned-source rebuild' if mode=='rebuild' else 'focused restoring theorem statement check','--']+cmd
with (O/'scope.log').open('w') as log:a=subprocess.run(launch,env=dict(os.environ,PV_REV=inp['source_revision']),stdout=log,stderr=subprocess.STDOUT)
rp=O/'receipt/receipt.json'
if not rp.exists():
 if (O/'barrier.json').exists() and json.load(open(O/'barrier.json')).get('allowed') is not True:cd.write_text(json.dumps(dict(until=time.time()+180)));sys.exit(78)
 raise SystemExit(('infrastructure failure',str(O)))
log=''.join((O/('receipt/'+x)).read_text(errors='replace') for x in ['stdout.log','stderr.log']);(O/'lean-output.log').write_text(log)
axioms=re.findall(r"'[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",log,re.S)
z=dict(attempt=n,module=module,mode=mode,row=m if mode=='check' else None,source_sha256=ss,source_revision=inp['source_revision'],exit=a.returncode,elaboration_failed=a.returncode!=0 and not bool(re.search(r"^.*:1:0: error: object file .* does not exist",log,re.M)),environment_failed=a.returncode!=0 and bool(re.search(r"^.*:1:0: error: object file .* does not exist",log,re.M)),object_sha256=sha(out) if a.returncode==0 else None,axioms=axioms)
(O/'result.json').write_text(json.dumps(z,indent=2)+'\n');rec=json.load(open(rp));rec.update(source_revision=inp['source_revision'],source_sha256=ss,target=module,print_axioms=axioms,dependencies_sha256=hashlib.sha256(json.dumps(pre,sort_keys=True).encode()).hexdigest());rp.write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(z),flush=True);sys.exit(a.returncode)
