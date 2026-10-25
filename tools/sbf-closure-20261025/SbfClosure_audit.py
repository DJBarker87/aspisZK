"""One focused bounded consistency audit of own preparation export only."""
import hashlib,io,json,os,pathlib,resource,stat,sys,tarfile,time,traceback
resource.setrlimit(resource.RLIMIT_AS,(536870912,536870912));os.umask(0o077)
P=pathlib.Path;B=P('/home/dombarker/project-offloads/codex-cx-sbf-recapture-20261024/SbfClosure-20261025-v1');O=B/'audit-v1';t=time.monotonic();checks=[]
r=dict(command=sys.orig_argv,print_axioms='N/A: no theorem/import/Lean execution',address_space_limit_bytes=536870912)
def check(label,value):
 if not value:raise AssertionError(label)
 checks.append(label)
def seal(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(1024**2):h.update(b)
 return dict(bytes=p.stat().st_size,sha256=h.hexdigest())
def put(name,x):
 b=(json.dumps(x,indent=2,sort_keys=True)+'\n').encode();assert len(b)<5000000
 with (O/name).open('xb') as f:f.write(b)
 return seal(O/name)
try:
 check('own parent',B.resolve()==B and B.stat().st_uid==1000 and stat.S_IMODE(B.stat().st_mode)==0o700 and (B/'OWNER').read_text()=='SbfClosure 20261025\n')
 cg=P('/sys/fs/cgroup');reservations=[]
 def visit(p):
  if p!=cg and 'populated 1' not in (p/'cgroup.events').read_text():return
  cap=(p/'memory.max').read_text().strip() if (p/'memory.max').exists() else 'max'
  if cap!='max':reservations.append((str(p),int(cap)));return
  for q in p.iterdir():
   if q.is_dir():visit(q)
 visit(cg);check('bounded prep reservation <55GiB',sum(x[1] for x in reservations)+536870912<55*1024**3)
 r['reservation_observation']=reservations;O.mkdir(mode=0o700);files=[];total=0
 with tarfile.open(fileobj=sys.stdin.buffer,mode='r|') as tar:
  for m in tar:
   p=pathlib.PurePosixPath(m.name)
   check('export canonical '+m.name,not p.is_absolute() and '..' not in p.parts and str(p)==m.name.rstrip('/'))
   if m.isdir():continue
   check('own text export '+m.name,m.isfile() and m.name.startswith(('tools/sbf-closure-20261025/','evidence/sbf-closure-20261025/')) and m.size<5000000)
   total+=m.size;check('bounded export total',total<32*1024**2)
   dst=O/m.name;dst.parent.mkdir(parents=True,exist_ok=True)
   with tar.extractfile(m) as f,dst.open('xb') as out:
    while b:=f.read(1024**2):out.write(b)
   files.append(dict(path=m.name,**seal(dst)))
 E=O/'evidence/sbf-closure-20261025';T=O/'tools/sbf-closure-20261025'
 def read(name):return json.loads((E/name).read_text())
 r['source_revision']=(E/'REVISION').read_text().strip();r['dependencies']=files
 check('source revision',len(r['source_revision'])==40)
 for name in ('collect-manifest.json','collect-v2-manifest.json'):
  for x in read(name)['files']:
   check('collection seal '+x['path'],seal(E/x['path'])=={k:x[k] for k in ('bytes','sha256')})
 tests=read('synthetic-tests.receipt.json')
 check('39 actual synthetic checks',tests['exit']==0 and tests['result']['count']==39 and len(tests['result']['tests'])==39)
 check('no privileged backend test',not tests['result']['privileged_backend_executed'] and not tests['result']['namespace_executed'])
 for script in ('SbfClosure_setup.py','SbfClosure_trace.py','SbfClosure_test.py'):
  check('tested source pin '+script,seal(T/script)==tests['helpers'][script])
 check('setup approval disabled','APPROVED_MANIFEST_SHA256 = ()' in (T/'SbfClosure_setup.py').read_text())
 check('setup GO refuses','actual GO schema/freshness integration still blocked' in (T/'SbfClosure_setup.py').read_text())
 inv=read('inventory.receipt.json');si=read('static-inputs.json');plan=read('future-plan.json')
 check('changed inventory passed',inv['exit']==0)
 check('source/manifests/lock counts',len(si['manifest_documents'])==17 and si['lock_packages']==444 and si['locked_registry_packages']==428 and si['prepared']==123 and len(si['absent_from_prepared'])==305)
 for x in si['absent_from_prepared']:check('missing locked checksum '+x['name']+x['version'],len(x['checksum'])==64 and x['source']=='registry+https://github.com/rust-lang/crates.io-index')
 pins=['f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4','63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299','121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548']
 check('three unchanged ELF pins',[x['expected_sha256'] for x in plan['builds']]==pins)
 for x in plan['builds']:
  before=x['environment_before'];after=x['environment'];mode=x['mode']
  check(mode+' only explicit proposed optimization change',{k:v for k,v in after.items() if k!='CARGO_PROFILE_RELEASE_BUILD_OVERRIDE_OPT_LEVEL'}==before and after['CARGO_PROFILE_RELEASE_BUILD_OVERRIDE_OPT_LEVEL']=='3')
  check(mode+' -j4',x['command'][x['command'].index('-j')+1]=='4')
  check(mode+' clean env-i',x['exact_clean_inner_command']==['/usr/bin/env','-i',*[k+'='+v for k,v in sorted(after.items())],*x['command']])
 check('zero execution budgets',all(x==0 for x in plan['budgets'].values()))
 candidates=[]
 for shard in read('public-input-candidates.json')['shards']:
  check('candidate shard '+shard['path'],seal(E/shard['path'])=={k:shard[k] for k in ('bytes','sha256')})
  candidates.extend(read(shard['path']))
 source=[x for x in candidates if x['set']=='frozen-source' and '/src/' in x['logical']]
 check('7978 actual source records plus wrapper and3 evidence files',len(source)==7978 and sum(x['set']=='frozen-source' for x in candidates)==7982)
 # Refined input list excludes three preparation-only metadata files and relabels
 # wrapper; original raw candidate shards remain unchanged as acquisition evidence.
 refined=[x for x in candidates if x['set']!='frozen-source' or '/src/' in x['logical'] or x['logical'].endswith('/rustc-diagnostics.py')]
 for x in refined:
  if x['set']=='frozen-source' and x['logical'].endswith('/rustc-diagnostics.py'):x['set']='diagnostic-wrapper'
 r['refined_input_shards']=[]
 for i in range(0,len(refined),1000):
  name='SbfClosure-inputs-%02d.json'%(i//1000);r['refined_input_shards'].append(dict(path=name,**put(name,refined[i:i+1000])))
 check('native candidate2592',len(read('native-public-packages.json')['files'])==2592)
 dso=read('static-dso-closure.json');check('45 static DSO objects no unresolved candidate sonames',len(dso['objects'])==45 and dso['unresolved']==[])
 pub=read('public-finish.stdout.json');check('registry16 default build scripts observed',pub['exit']==0 and len(pub['registry_scripts'])==16)
 sdk=read('sdk.stdout.json');check('SDK external link blocked',sdk['exit']==1 and '/v2.3.3/criterion' in sdk['error'])
 r['operation_associations']=[]
 # Earlier receipts display helper-name placeholder command. Reconstruct exact
 # -c argv from retained literal source; never invent missing transport metrics.
 for label,script,rev in [('host-v1','SbfClosure_host.py','6d596146be'),('analysis-v1','SbfClosure_analyze_host.py','0de1bb48d1'),('continuation-v2','SbfClosure_inventory_continue.py','a17efca47b'),('public-finish','SbfClosure_public_finish.py','70c9d32784'),('sdk','SbfClosure_sdk.py','2a2c3006ab')]:
  body=(T/script).read_text()
  r['operation_associations'].append(dict(operation=label,source_revision=rev,helper=seal(T/script),exact_host_command=['python3','-B','-c',body],transport=['ssh','-o','BatchMode=yes','-o','ConnectTimeout=10','dombarker@100.108.41.90','python3 -B -c <POSIX shell-quoted exact helper bytes above>'],transport_metrics='unavailable separately; shell tool wall included other commands',interpreter_association='host-v1 runtime interpreter pin reused; unchanged identity was not freshly checked for every operation',receipt_stdout=seal(E/(label+'.stdout.json'))))
 r.update(exit=0,checks=checks,claim='Own preparation consistency only. Partial finite inputs, static package/DSO/source inventory and39 synthetic checks. No setup/trace/loader/offline resolver/cache/build/security closure.',before_after='unchanged theorem/security statements and premises; no new trust assumptions',remaining=['SDK external criterion link policy/static selected subset','exact private tool/source/runtime root and same-uid exclusion','ResourceAdmit actual GO integration and new allocation','real syscall tests/tiny privileged probe after manager review','whole-workspace offline resolution','trace unsupported syntax/absence/readlink/fd/output/cache joins','all release/native/Std/P7/extraction/effect/security joins'])
except Exception as e:r.update(exit=1,error=repr(e),traceback=traceback.format_exc(),checks=checks)
u=resource.getrusage(0);r.update(wall_seconds=time.monotonic()-t,peak_rss_kib=u.ru_maxrss,swap=u.ru_nswap,interpreter=dict(path=sys.executable,version=sys.version,**seal(P(sys.executable).resolve())))
put('SbfClosure-audit.json',r)
# Output audit and refined shards only, small individually. No copied binaries.
with tarfile.open(fileobj=sys.stdout.buffer,mode='w|') as tar:
 for name in ['SbfClosure-audit.json']+[x['path'] for x in r.get('refined_input_shards',[])]:tar.add(O/name,arcname=name,recursive=False)
sys.exit(r['exit'])
