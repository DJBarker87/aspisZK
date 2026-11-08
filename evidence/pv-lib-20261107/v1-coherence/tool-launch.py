"""Admitted serial tool compile, statement comparison, or sole final raw audit."""
import pathlib,json,subprocess,shlex,sys,time
E=pathlib.Path('evidence/pv-lib-20261107/v1-coherence');V='/home/dombarker/project-offloads/codex-pv-lib-slice-20261107/v1-coherence';host='dombarker@100.108.41.90';a=int(sys.argv[1]);mode=sys.argv[2]
assert 56500<=a<=56589 if not mode.startswith('audit') else 56590<=a<=56599
assert not (E/f'turn-{a}.json').exists()
cmd=['ssh',host,'STREAMB_SLOTS=3 /home/dombarker/streamb-slots/turn.sh'];t=time.time();r=subprocess.run(cmd,capture_output=True,text=True);turn=dict(attempt=a,command=cmd,exit=r.returncode,wall=time.time()-t,stdout=r.stdout,stderr=r.stderr);(E/f'turn-{a}.json').write_text(json.dumps(turn,indent=2));assert r.returncode==0
files={}
for name in ['PV_LIB_V1_StatementSnapshot','PV_LIB_V1_RawAudit4','PV_LIB_V1_ModuleDeclarations2','PV_LIB_V1_DeclarationCohort','PV_LIB_V1_StatementAlpha','PV_LIB_V1_RawAuditNarrow']:files['sources-canonical/'+name+'.lean']=pathlib.Path('lean',name+'.lean').read_text()
for name in ['run-snapshots.py']:files[name]=(E/name).read_text()
files['AUDIT_ROOTS.json']=(E/'AUDIT_ROOTS.json').read_text()
files['INVENTORY.json']=(E/'INVENTORY.json').read_text()
files['ACTIVE_INVENTORY.json']=(E/'ACTIVE_INVENTORY.json').read_text()
files['run-thread-audit.py']=subprocess.check_output(['git','show','5e397cb3878:tools/pv-lib-20261107/run-thread-audit.py'],text=True)
files['ROOT_BATCHES.json']=(E/'ROOT_BATCHES.json').read_text()
for b in json.loads(files['ROOT_BATCHES.json'])['batches']:
 files['sources-canonical/'+b['name']+'.lean']=pathlib.Path('lean',b['name']+'.lean').read_text()
files['compile-root-batches.py']=(E/'compile-root-batches.py').read_text()
files['run-final-audit.py']=(E/'run-final-audit.py').read_text()
files['NARROW_ROOT_BATCHES.json']=(E/'NARROW_ROOT_BATCHES.json').read_text()
files['FAMILY_ROOT_BATCHES.json']=(E/'FAMILY_ROOT_BATCHES.json').read_text()
files['FINAL_ROOT_BATCHES.json']=(E/'FINAL_ROOT_BATCHES.json').read_text()
code=r'''
import pathlib,json,sys,subprocess,time,hashlib,re,os
x=json.load(sys.stdin);a=x['attempt'];mode=x['mode'];V=pathlib.Path('HOST');E=V/'evidence';O=V/'objects-canonical'
assert not (E/f'receipt-{a}.json').exists()
for name,s in x['files'].items():
 p=V/name
 if name.startswith('sources-canonical/') and (O/(p.stem+'.olean')).exists():assert p.read_text()==s
 if not p.exists() or p.read_text()!=s:p.write_text(s)
(V/'SNAPSHOT_PLAN.json.xz').write_bytes(bytes.fromhex(x['snapshot_plan']))
(E/f'turn-{a}.json').write_text(json.dumps(x['turn']))
pat=re.compile(r'(^|[-_])'+str(a)+r'([-_.]|$)');hits=[]
for job in V.parents[1].glob('codex-*'):
 for d,dirs,files in os.walk(job/'evidence'):hits += [os.path.join(d,n) for n in files if pat.search(n)]
sent=V.parents[1]/'r1-privacy-build-integration-20261019/evidence/sent.txt';sent_hits=[l for l in sent.read_text().splitlines() if len(l.split())>2 and l.split()[2]==str(a)]
assert not hits and not sent_hits,(hits,sent_hits)
(E/f'id-audit-{a}.json').write_text(json.dumps(dict(hits=hits,sent=sent_hits)))
scanner=V.parents[1]/'codex-pv-runjoin-20261026/reservation-existing.py'
with (E/f'admission-{a}.log').open('w') as f:r=subprocess.run(['python3',str(scanner),str(E/f'admission-{a}.json')],stdout=f,stderr=subprocess.STDOUT)
admit=json.load(open(E/f'admission-{a}.json'))
if r.returncode or admit.get('allowed') is not True:
 (E/f'receipt-{a}.json').write_text(json.dumps(dict(exit=r.returncode,accepted=False,refusal=True,epoch=time.time())));sys.exit(78)
if mode in ['compile-snapshot','compile-audit','compile-declarations','compile-compatibility','compile-alpha','compile-narrow']:
 m={'compile-snapshot':'PV_LIB_V1_StatementSnapshot','compile-audit':'PV_LIB_V1_RawAudit4','compile-declarations':'PV_LIB_V1_ModuleDeclarations2','compile-compatibility':'PV_LIB_V1_DeclarationCohort','compile-alpha':'PV_LIB_V1_StatementAlpha','compile-narrow':'PV_LIB_V1_RawAuditNarrow'}[mode]
 assert not (O/(m+'.olean')).exists()
 inner=['python3','/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence/run2.py',str(V/'J.json'),str(O),str(V/'sources-canonical'),str(O/(m+'.olean')),str(V/'sources-canonical'/(m+'.lean')),'7000']
elif mode in ['cache-imports','declarations','compatibility','alpha']:
 plan=json.load(open(V/'PLAN.json'));paths=sorted(str(p) for p in O.glob('PV_*.olean'))
 (V/'cache-imports-request.json').write_text(json.dumps(paths))
 env=json.load(open(V/'J.json'))
 runner="import json,os,sys;v=json.load(open(sys.argv[1]));\nfor k,x in v.items():\n if x is None:os.environ.pop(k,None)\n else:os.environ[k]=x\nos.execv(v['LEAN'],[v['LEAN'],'-j1','-M7000','-DElab.async=false','--run',sys.argv[2],'imports',sys.argv[3]])\n"
 if mode in ['declarations','compatibility','alpha']:runner=runner.replace("'imports',sys.argv[3]","sys.argv[3]")
 (V/'cache-imports-run.py').write_text(runner)
 if mode=='compatibility':
  import lzma
  report=json.loads(lzma.decompress((E/'ROOT_IMPORT_PREFLIGHT.json.xz').read_bytes()))
  paths=[str(O/(m+'.olean')) for m in report['closure'] if (O/(m+'.olean')).exists()]
  (V/'cache-imports-request.json').write_text(json.dumps(dict(paths=paths,names=list(report['duplicate_declarations']))))
 if mode=='alpha':(V/'cache-imports-request.json').write_bytes((V/'TYPE_PAIRS.json').read_bytes())
 inner=['python3',str(V/'cache-imports-run.py'),str(V/'J.json'),str(V/('sources-canonical/PV_LIB_V1_ModuleDeclarations2.lean' if mode=='declarations' else 'sources-canonical/PV_LIB_V1_DeclarationCohort.lean' if mode=='compatibility' else 'sources-canonical/PV_LIB_V1_StatementAlpha.lean' if mode=='alpha' else 'sources-canonical/PV_LIB_V1_StatementSnapshot.lean')),str(V/'cache-imports-request.json')]
elif mode=='compile-batches':inner=['python3',str(V/'compile-root-batches.py'),str(a)]
elif mode=='snapshots':inner=['python3',str(V/'run-snapshots.py'),str(a)]
elif mode in ['audit','audit-focus']:
 plan=json.load(open(V/'PLAN.json'));assert all((O/(m+'.olean')).exists() for m in plan['order'])
 inner=['timeout','7200','python3',str(V/'run-final-audit.py'),str(a)]+(['focus'] if mode=='audit-focus' else [])
else:raise RuntimeError(mode)
cmd=['systemd-run','--user','--scope','--quiet',f'--unit=pv-lib-{a}','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','/usr/bin/time','-v','-o',str(E/f'time-{a}.log')]+inner
with (E/f'out-{a}.log').open('w') as f:
 r=subprocess.Popen(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,cwd=V)
 for line in r.stdout:
  f.write(line);f.flush()
  if mode not in ['cache-imports','declarations','compatibility','alpha'] or not line.startswith('{'):print(line,end='',flush=True)
 r.wait()
rec=dict(attempt=a,target=mode,source_revision=json.load(open(V/'PLAN.json'))['revision'],tools_revision=x['tools_revision'],exit=r.returncode,accepted=r.returncode==0,command=cmd,inputs_sha256={n:hashlib.sha256(s.encode()).hexdigest() for n,s in x['files'].items()})
for l in (E/f'time-{a}.log').read_text().splitlines():
 for k,field in [('Maximum resident set size (kbytes):','peak_rss_kbytes'),('Swaps:','swaps'),('Elapsed (wall clock) time (h:mm:ss or m:ss):','wall')]:
  if k in l:rec[field]=l.split(k)[1].strip()
rec['axioms_summary_based']=[l for l in (E/f'out-{a}.log').read_text().splitlines() if 'axioms' in l]
(E/f'receipt-{a}.json').write_text(json.dumps(rec,indent=2));print(json.dumps({k:v for k,v in rec.items() if k!='axioms_summary_based'}),flush=True);sys.exit(r.returncode)
'''.replace('HOST',V)
payload=dict(attempt=a,mode=mode,turn=turn,files=files,snapshot_plan=(E/'SNAPSHOT_PLAN.json.xz').read_bytes().hex(),tools_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
if len(sys.argv)>3 and sys.argv[3]=='detach':
 stage=r"""
import pathlib,json,sys,subprocess,hashlib
x=json.load(sys.stdin);V=pathlib.Path('HOST');a=x['payload']['attempt'];E=V/'evidence'
p=V/f'detached-launch-{a}.py';data=V/f'detached-payload-{a}.json';assert not p.exists() and not data.exists()
p.write_text(x['code']);data.write_text(json.dumps(x['payload']))
log=E/f'detached-transport-{a}.log'
with data.open('r') as inp,log.open('w') as out:
 child=subprocess.Popen(['python3',str(p)],stdin=inp,stdout=out,stderr=subprocess.STDOUT,start_new_session=True,close_fds=True,cwd=V)
r=dict(attempt=a,detached=True,pid=child.pid,launcher_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),payload_sha256=hashlib.sha256(data.read_bytes()).hexdigest(),stdout_file=str(log),all_stdio_host_files=True)
(E/f'detached-ack-{a}.json').write_text(json.dumps(r));print(json.dumps(r))
""".replace('HOST',V)
 # The detached controller must have a regular stdout file, never an SSH pipe.
 code=code.replace("x=json.load(sys.stdin);", "import stat;assert stat.S_ISREG(os.fstat(1).st_mode);x=json.load(sys.stdin);")
 r=subprocess.run(['ssh',host,'python3 -c '+shlex.quote(stage)],input=json.dumps(dict(code=code,payload=payload)),text=True,capture_output=True)
 (E/f'transport-{a}.json').write_text(json.dumps(dict(exit=r.returncode,stdout=r.stdout,stderr=r.stderr,detached=True),indent=2));print(r.stdout,r.stderr);sys.exit(r.returncode)
r=subprocess.Popen(['ssh',host,'python3 -c '+shlex.quote(code)],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True);r.stdin.write(json.dumps(payload));r.stdin.close();lines=[]
for line in r.stdout:lines.append(line);print(line,end='',flush=True)
r.wait();(E/f'transport-{a}.json').write_text(json.dumps(dict(exit=r.returncode,stdout=''.join(lines),stderr=''),indent=2));sys.exit(r.returncode)
