#!/usr/bin/env python3
"""One focused offline receipt/provenance/scope audit, no build or remote call."""
import ast,hashlib,json,pathlib,resource,subprocess,time,sys
T=pathlib.Path(__file__).resolve().parent;R=T.parents[1];E=R/'evidence/sbf-recapture-prep-20261024';START=time.monotonic();checks=[];deps={};exit=0
BASE='009b61e61bf52dba92c4fbefae79702a938f05b3'
def sha(b):return hashlib.sha256(b).hexdigest()
def check(label,condition):
 checks.append(dict(check=label,passed=bool(condition)))
 if not condition:raise AssertionError(label)
def load(name):return json.loads((E/name).read_bytes())
def immutable(path):return subprocess.check_output(['git','show',BASE+':'+path])
try:
 for folder in [E,T]:
  for p in sorted(folder.iterdir()):
   if p.name=='audit.json':continue
   b=p.read_bytes();check('bounded text '+str(p.relative_to(R)),len(b)<=5000000 and b'\0' not in b);deps[str(p.relative_to(R))]=dict(sha256=sha(b),bytes=len(b))
 for p in T.glob('*.py'):ast.parse(p.read_text(),filename=str(p))
 check('all scripts parse',True)
 for name in ['init','cache-observe','download','source-verify','archive']:
  r=load(name+'.stdout.json');tr=load(name+'.transport.json')
  check(name+' transport exact',tr['exit']==0 and tr['stdout_sha256']==sha((E/(name+'.stdout.json')).read_bytes()))
  check(name+' success/noSwap/boundedRSS',r['receipt']['exit']==0 and r['receipt']['swaps']==0 and r['receipt']['peak_rss_kib']<512*1024)
  check(name+' retained script',r['receipt']['script_sha256'] in [sha((T/'SbfRecapturePrep_host.py').read_bytes()),sha((T/'SbfRecapturePrep_host_v1.py.txt').read_bytes())])
  check(name+' exact transport script pin',tr['script_sha256']==r['receipt']['script_sha256'])
  check(name+' comparison interpreter',r['receipt']['python_sha256']==load('metadata-pins.json')['comparison_runtime']['python_sha256'])
 d=load('download.stdout.json');check('one download exact size/hash',d['verified'] and len(d['attempts'])==1 and d['bytes']==519270959 and d['sha256']=='8b3861e93daf085ec12b65c4fac374d9bec4587a3de16871da6b08ab0c1d907e')
 a=load('archive.stdout.json');rows=load('archive-members.json');check('complete archive equality',a['full_equality'] and not a['differences'] and not a['extra_current_paths'] and a['members']==len(rows)==3828 and all(r['equal'] for r in rows))
 check('archive raw manifest exact',sha((E/'archive-members.json').read_bytes())==a['raw_manifest']['sha256'])
 index={r['path']:r for r in rows};check('unique archive paths',len(index)==len(rows))
 old=json.loads(immutable('evidence/sbf-identity-20261024/current-content.json'));prefix=old['root']+'/platform-tools/'
 for name,r in old['pins'].items():
  check('baseline remains exact '+name,name.startswith(prefix) and index[name[len(prefix):]].get('current_sha256')==r['sha256'] and index[name[len(prefix):]]['current_size']==r['bytes'])
 check('all packaged targets',all(any(r['path'].startswith('rust/lib/rustlib/'+target+'/lib/') for r in rows) for target in ['sbf-solana-solana','sbpf-solana-solana','sbpfv1-solana-solana','sbpfv2-solana-solana','x86_64-unknown-linux-gnu']))
 s10='docs/research/100bit-spend-path-20261013/evidence/s10-repin3-20261023/'
 b=immutable(s10+'source-inputs.json');m=json.loads(b);check('frozen manifest exact',sha(b)=='a84a528cfc4b294c603fe5381343cdaf9df0547467bcc94e61a67e5111adb9d1' and len(m['files'])==7978)
 files=load('materialized-files.json');source={r['path'][4:]:r for r in files if r['path'].startswith('src/')};check('source exact set',set(source)=={r['path'] for r in m['files']})
 tree={}
 for row in subprocess.check_output(['git','ls-tree','-rz',m['source_revision']]).split(b'\0'):
  if not row:continue
  header,name=row.split(b'\t',1);mode,kind,oid=header.decode().split();tree[name.decode()]=(mode,kind,oid)
 for r in m['files']:
  q=source[r['path']];mode,kind,oid=tree[r['path']]
  check('frozen source '+r['path'],q['sha256']==r['sha256'] and q['bytes']==r['bytes'] and kind=='blob' and q['git_blob']==oid and q['mode']==(int(mode,8)&0o777))
 sv=load('source-verify.stdout.json');check('independent materialization verification',sv['verified_records']==7978 and sv['full_content_type_mode_check'] and not sv['extra_source_files'])
 check('materialized raw manifest exact',sha((E/'materialized-files.json').read_bytes())==sv['materialized_manifest']['sha256'])
 c=load('cache-observe.stdout.json');check('cache step failclosed',not c['allowed_to_enter'] and c['permission_denied_pids'] and not c['cache_hash_or_copy_run'])
 plan=load('future-plan.json');old=json.loads(immutable('evidence/sbf-identity-20261024/recapture-plan.json'))
 def relocate(x):
  if isinstance(x,str):return x.replace(old['stage'],plan['stage']).replace('--unit=sbf-identity-20261024-','--unit=sbf-recapture-20261024-')
  if isinstance(x,list):return [relocate(a) for a in x]
  if isinstance(x,dict):return {k:relocate(v) for k,v in x.items()}
  return x
 for before,after in zip(old['builds'],plan['builds']):
  for field in ['command','environment','unset_environment','scope_command','cwd','output','linked_output','expected_sha256']:
   check('exact relocated '+after['mode']+' '+field,relocate(before[field])==after[field])
  check('unchanged historical predecessor '+after['mode'],before['historical_predecessor']==after['historical_predecessor'])
  cmd=[sys.executable,str(T/'SbfRecapturePrep_runner.py'),after['mode'],'--run'];r=subprocess.run(cmd,capture_output=True)
  check('runner refuses '+after['mode'],r.returncode==2 and b'DENIED' in r.stderr)
 check('no build/readiness claim',plan['builds_run']==0 and plan['execution_blockers'] and plan['resources']['scope_launches']==0 and plan['headroom'].startswith('UNKNOWN'))
 for r in load('metadata-pins.json')['immutable_inputs']:check('immutable reuse pin '+r['path'],sha(immutable(r['path']))==r['sha256'])
 for name,script in [('metadata-pins.json','SbfRecapturePrep_metadata.py'),('plan.receipt.json','SbfRecapturePrep_plan.py'),('collect.receipt.json','SbfRecapturePrep_collect.py'),('materialize.transport.json','SbfRecapturePrep_materialize.py')]:
  r=load(name);r=r.get('receipt',r);check('script pin '+script,r['script_sha256']==sha((T/script).read_bytes()) and r['exit']==0 and r['swaps']==0)
 scope=subprocess.check_output(['git','diff','--name-only',BASE,'HEAD'],text=True).splitlines()+subprocess.check_output(['git','ls-files','--others','--exclude-standard'],text=True).splitlines()
 check('assigned paths only',all(p.startswith(('tools/sbf-recapture-prep-20261024/','evidence/sbf-recapture-prep-20261024/')) for p in scope))
 check('assigned branch',subprocess.check_output(['git','branch','--show-current'],text=True).strip()=='codex/cx-sbf-recapture-prep-20261024')
except Exception as e:
 exit=1;checks.append(dict(error=type(e).__name__+': '+str(e),passed=False))
finally:
 u=resource.getrusage(0);c=resource.getrusage(resource.RUSAGE_CHILDREN)
 r=dict(schema='SbfRecapturePrep-focused-audit-v1',checks=checks,check_count=len(checks),dependencies=deps,budgets=dict(lean=0,kani=0,extraction=0,backend=0,rust=0,compiler_build=0,sbf=0,consumer=0,full_manifest=0),receipt=dict(command=[sys.executable,str(T/'SbfRecapturePrep_audit.py')],exit=exit,wall_seconds=time.monotonic()-START,peak_rss_bytes=u.ru_maxrss,children_peak_rss_bytes=c.ru_maxrss,swaps=u.ru_nswap+c.ru_nswap,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),script_sha256=sha(pathlib.Path(__file__).read_bytes()),print_axioms='N/A: no theorem/import/proof/compiler/build gate'))
 (E/'audit.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(dict(checks=len(checks),receipt=r['receipt'],failure=checks[-1] if exit else None),indent=2))
sys.exit(exit)
