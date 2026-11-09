"""NFX-owned serial client for unchanged S2W launcher; no shared tool edits."""
from pathlib import Path
import subprocess,json,sys,time,hashlib,shlex,lzma,re,os,atexit
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90'
B='/home/dombarker/project-offloads/codex-cx-integrate-20261111';C='/home/dombarker/project-offloads/codex-cx-integrate-20261111';W='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025';T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
if (E/'NNH_HOLD').exists():sys.exit(75)
guard=E/'NNH_CLIENT_ACTIVE'; fd=os.open(guard,os.O_CREAT|os.O_EXCL|os.O_WRONLY);os.write(fd,str(os.getpid()).encode());os.close(fd);atexit.register(lambda:guard.unlink(missing_ok=True))
a,kind,target=sys.argv[1:];assert re.fullmatch('NNH_L[0-9]{3}',a) and 1<=int(a[-3:]) and not (E/a).exists()
# S4 rev4: new outputs use a private overlay; historical objects remain read-only fallback.
# Budget actual submissions, including unresolved ones, rather than ID suffixes.
# Run 5 grants 160 fresh scopes after 700 terminal submissions.
used=set()
for n in ['NNH_ATTEMPTS.jsonl','NNH_TRANSPORT.jsonl']:
 p=E/n
 if not p.exists():continue
 for line in p.read_text().splitlines():
  row=json.loads(line)
  if 'exit_status' in row or row.get('submitted') is True:used.add(row['attempt'])
assert len([x for x in used if int(x[-3:]) >= 930]) < 41, 'Run7 40+1 scope budget exhausted'
big = kind=='lean16'
if big:
 assert not any(json.loads(l).get('module_kind')=='lean16' for l in (E/'NNH_ATTEMPTS.jsonl').read_text().splitlines() if l.strip()), 'the one 16GiB scope is already used'
 assert target in ['TAS_G0_COMBINED_IMPORT'], '16GiB scope is for the final combined import only'
 kind='lean'
else:
 assert len([x for x in used if int(x[-3:]) >= 930]) < 40, 'Run7 40-scope budget exhausted'

def ssh(code,data=None,submitted=False):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,code],input=data,capture_output=True,text=True)
  with (E/'NNH_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=retry,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
  if r.returncode!=255:return r
  if submitted:raise RuntimeError('Submitted; recover read-only, never resubmit')
  if retry<10:time.sleep(60)
 raise RuntimeError('Transport exhausted')
while True:
 r=ssh('python3',"""import subprocess,pathlib,json
units=subprocess.check_output(['systemctl','--user','list-units','--type=scope','--state=running','--no-legend','--no-pager'],text=True).splitlines();found=[]
for line in units:
 unit=line.split()[0];cg=subprocess.check_output(['systemctl','--user','show',unit,'-p','ControlGroup','--value'],text=True).strip();p=pathlib.Path('/sys/fs/cgroup'+cg)
 try:pids=(p/'cgroup.procs').read_text().split()
 except FileNotFoundError:continue
 for pid in pids:
  try:cwd=str(pathlib.Path('/proc/'+pid+'/cwd').resolve(strict=True))
  except (FileNotFoundError,PermissionError,ProcessLookupError):continue
  if cwd.startswith('/home/dombarker/project-offloads/codex-'):found.append(unit);break
lean=subprocess.run(['pgrep','-c','-x','lean'],capture_output=True,text=True).stdout.strip() or '0'
print(json.dumps(dict(scopes=found,count=len(found),lean_procs=int(lean))))
""")
 assert r.returncode==0,r.stderr
 share_info=json.loads(r.stdout)
 with (E/'NNH_ATTEMPTS.jsonl').open('a')as f:f.write(json.dumps(dict(attempt=a,event='share_check' if share_info['count']<6 and share_info['lean_procs']<6 else 'wait',reason='Stream A scope share',host=share_info))+'\n')
 if share_info['count']<6 and share_info['lean_procs']<6:break
 time.sleep(180)
for disk_retry in range(7):
 disk=ssh('python3',"import shutil,json;print(json.dumps(shutil.disk_usage("+repr(B)+")._asdict()))")
 assert disk.returncode==0,disk.stderr
 disk_info=json.loads(disk.stdout)
 (E/(a+'-disk-'+str(disk_retry)+'.json')).write_text(json.dumps(disk_info))
 if disk_info['free']>=40_000_000_000:break
 if disk_retry==6:raise RuntimeError('STOP host free below40GB after six waits')
 for _ in range(10):time.sleep(60)
for retry in range(11):
 r=ssh('python3',f'''from pathlib import Path
import subprocess,sys
b=Path({B!r})
with (b/{(a+'-barrier-'+str(retry)+'.log')!r}).open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/{(a+'-reservation.json')!r})],stdout=f,stderr=subprocess.STDOUT)
p=b/{(a+'-reservation.json')!r}; print(p.read_text() if p.exists() else 'MISSING');sys.exit(r.returncode)
''')
 (E/(a+f'-barrier-{retry}.log')).write_text(r.stdout+r.stderr)
 try:ad=json.loads(r.stdout)
 except json.JSONDecodeError:
  if retry==0:time.sleep(30);continue
  raise RuntimeError('STOP missing admission')
 (E/(a+'-admission.json')).write_text(json.dumps(dict(exit=r.returncode,reservation=ad)))
 if r.returncode==0 and ad.get('allowed') is True:break
 if (r.returncode==78 or ad.get('allowed') is False) and retry<10:
  with (E/'NNH_ATTEMPTS.jsonl').open('a')as f:f.write(json.dumps(dict(attempt=a,event='wait',reason='reservation refusal',exit=r.returncode,reservation=ad))+'\n')
  print('reservation wait',flush=True);time.sleep(180);continue
 raise RuntimeError('STOP admission')
files={};sources=[]
if kind=='lean':
 if target=='NNH_OwnerStatements':files['NNH_AUDIT_ROOTS.json']=(E/'NNH_AUDIT_ROOTS.json').read_text()
 n='NNH_generated/'+target.replace('.','/')+'.lean';files[n]=((E/(target+'.lean'))if (E/(target+'.lean')).exists()else(E/'NNH_dependency_inputs'/(target+'.lean'))).read_text();sources=[n]
 command=[T+'/bin/lake','env','lean','-j1','-M15000' if big else '-M7000','-DElab.async=false','-R','NNH_generated','-o','NNH_R7_objects/'+target.replace('.','/')+'.olean',n]
 if target in ['NNH_Driver','NNH_ProofDriver','NNH_PoolProofDriver','NNH_PoolDriver','NNH8_RuntimeScan']:command+=['-c','NNH_native/'+target+'.c']
elif kind=='rawaudit':
 roots,module=target.split('@')
 sources=['NNH_R7_raw_audit.py'];files['NNH_R7_raw_audit.py']=(E/'NNH_R7_raw_audit.py').read_text()
 command=['python3','NNH_R7_raw_audit.py',a,roots,module]
elif kind=='scan':
 sources=['NNH8_EXPECTED_IMPORTS.jsonl'];files[sources[0]]=(E/sources[0]).read_text()
 command=['NNH_native/NNH8_RuntimeScan','scan',a+'/NNH8_LOADED_scan.jsonl']
elif kind=='link':
 sources=['NNH_native/'+target+'.c']+([] if target=='NNH8_RuntimeScan' else ['NNH_native/NFA_WALKER.c','NNH_native/NFA_MemoryLimit.c'])
 command=[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NNH_native/'+target,*sources]
elif kind=='audit':
 sources=['NNH_AUDIT_ROOTS.json','NNH_AUDIT_MODULES.json','NNH_RAW_BINARY_PIN.json','NNH_RAW_DRIVER_SOURCE.txt']
 if target=='retention':sources += ['NNH_finalize_host.py','NNH_NND_IMPORTS.json','NNH_SEED_WAdm_Fissioned.json','NNH_RESUME_LIBRARY_IMPORTS.json','NNH_RESUME_DEPENDENCY_IMPORTS.json','NNH_RESUME_FLAT_IMPORTS.json','NNH_LANE_IMPORTS.json','NNH_FINISH_DEPENDENCY_IMPORTS.json','NNH_FINISH_IMPORTS.json','NNH_SEED_NMT_tx1.json']
 for n in sources:files[n]=(E/n).read_text()
 files['NLX_AUDIT_ROOTS.json']=(E/'NNH_AUDIT_ROOTS.json').read_text()
 files['NLX_AUDIT_MODULES.json']=(E/'NNH_AUDIT_MODULES.json').read_text()
 sources += ['NLX_AUDIT_ROOTS.json','NLX_AUDIT_MODULES.json']
 command=['python3','NNH_finalize_host.py'] if target=='retention' else ['NNH_native/NNH_ProofDriver',target]

else:raise ValueError(kind)
overlays=json.loads((E/'NNH_RUN7_PATHS.json').read_text())
config=dict(attempt=a,kind=kind,module=target,sources=sources,command=command,env=dict(LEAN_SYSROOT=T,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',TMPDIR=B+'/NNH_tmp',CARGO_TARGET_DIR=B+'/NNH_target',LEAN_PATH=':'.join([B+'/NNH_R7_objects']+overlays)),timeout=600 if big else 180,module_kind='lean16' if big else kind,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,deps_fingerprint={},expected_time='Raw ax2 traversal with pinned ledger30 walker' if kind=='rawaudit' else 'NFX loaded-closure scan' if kind=='scan' else 'Focused import elaboration' if kind=='lean' else 'Optimized linker' if kind=='link' else 'Raw ax2 traversal / coherence scan')
files[a+'.json']=json.dumps(config)
r=ssh('python3',f'''from pathlib import Path
import json,hashlib,re,shutil
b=Path({B!r});files=json.loads({json.dumps(files)!r})
for n,t in files.items():
 p=b/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
(b/'NNH_native').mkdir(exist_ok=True);(b/'NNH_R4_objects').mkdir(exist_ok=True);(b/'NNH_R7_objects').mkdir(exist_ok=True);(b/'NNH_tmp').mkdir(exist_ok=True)
(b/'NNH_R7_objects'/{target.replace('.', '/')!r}).parent.mkdir(parents=True,exist_ok=True)
for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
 p=b/'NNH_native'/n
 if not p.exists():shutil.copy2('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NGJ_native_seed/'+n,p)
x=json.loads((b/{(a+'.json')!r}).read_text());roots=x['env']['LEAN_PATH'].split(':');pins={{}}
modules=[]
if x['kind']=='lean':modules += re.findall(r'^import ([\\w.]+)',(b/x['sources'][0]).read_text(),re.M)
elif x['kind']=='rawaudit':modules += [x['command'][4]]
elif x['kind']=='scan':modules += ['TAS_G0_COMBINED_IMPORT']
elif x['kind']=='audit':modules += ['NNH_FINAL_COMBINED_IMPORT','NNH_ContinuationCombined'] if x['module']=='retention' else json.loads((b/'NNH_AUDIT_MODULES.json').read_text())[int(x['module'][5:])]
rels=set()
for root in roots:
 for stem in ['Aeneas','AeneasMeta']:
  p=Path(root)/stem
  if p.is_dir():rels.update(str(z.relative_to(root)) for z in p.rglob('*') if z.is_file() and any(str(z).endswith(s) for s in ['.olean','.olean.private','.olean.server','.ir']))
  if Path(root,stem+'.olean').is_file():rels.add(stem+'.olean')
rels.update(n.replace('.','/')+'.olean' for n in modules)
for rel in sorted(rels):
 p=next((Path(root)/rel for root in roots if (Path(root)/rel).is_file()),None)
 assert p is not None,rel
 for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if z.is_file():pins[str(z)]={{'path':str(z),'sha256':hashlib.sha256(z.read_bytes()).hexdigest()}}
if x['kind']=='audit':
 binary=json.loads((b/'NNH_RAW_BINARY_PIN.json').read_text());assert hashlib.sha256(Path(binary['destination']).read_bytes()).hexdigest()==binary['sha256'];x['raw_ax2_binary']=binary
x['deps_fingerprint']={{'selected_objects':pins,'cache_imports_manifest_sha256':hashlib.sha256((b/'NNH_CACHE_IMPORTS.json.xz').read_bytes()).hexdigest()}}
(b/{(a+'.json')!r}).write_text(json.dumps(x))
''');assert r.returncode==0,r.stderr
r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope '+('-p MemoryHigh=14G -p MemoryMax=16G' if big else '-p MemoryHigh=6G -p MemoryMax=8G')+' -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
r=ssh('python3',f'''from pathlib import Path
import json,hashlib
b=Path({B!r});a={a!r};names=[str(p.relative_to(b)) for p in (b/a).rglob('*') if p.is_file()]+[a+'.json']
if {kind!r}=='audit':names += [str(p.relative_to(b)) for p in b.glob('NEP_'+{target!r}+'_*') if p.is_file()]

out={{n:(b/n).read_text() for n in names}}
if {target!r}=='retention':
 for n in ['NNH_EXPORT.json','NNH_EXPORT_REJECTED.json','NNH_FINAL_HOST.json','NNH_CLOSURE_PINS.json.sha256']:out[n]=(b/n).read_text()
 out['NNH_CLOSURE_PINS.json.xz.hex']=(b/'NNH_CLOSURE_PINS.json.xz').read_bytes().hex()
if {target!r} in ['close','review-close','review-retention']:
 for n in ['NNH_PREDECESSOR_COMPARISON.json','NNH_EXPORT.json','NNH_TOOL_PINS.json','NNH_CLOSURE_PINS.json.sha256']:
  if (b/n).exists():out[n]=(b/n).read_text()
 if (b/'NNH_CLOSURE_PINS.json.xz').exists():out['NNH_CLOSURE_PINS.json.xz.hex']=(b/'NNH_CLOSURE_PINS.json.xz').read_bytes().hex()
if {target!r} in ['close','retention','review-retention']:
 if (b/'NNH_FINAL_HOST.json').exists():out['NNH_FINAL_HOST.json']=(b/'NNH_FINAL_HOST.json').read_text()
for name in ['NNH_Driver','NNH_ProofDriver','NNH_PoolProofDriver','NNH_PoolDriver']:
 p=b/'NNH_native'/name
 if p.is_file():out[a+'/'+name+'_BINARY_PIN.json']=json.dumps(dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
print(json.dumps(out))
''');assert r.returncode==0,r.stderr
for n,t in json.loads(r.stdout).items():
 p=E/n;p.parent.mkdir(parents=True,exist_ok=True)
 if n.endswith('.xz.hex'):
  (E/n[:-4]).write_bytes(bytes.fromhex(t));continue
 if n.startswith('NEP_') and n.endswith('_REACHABLE.txt'):
  raw=t.encode();(E/('NNH_'+n+'.sha256')).write_text(hashlib.sha256(raw).hexdigest()+'\n');(E/('NNH_'+n+'.xz')).write_bytes(lzma.compress(raw,preset=6 if len(raw)>20_000_000 else 1))
 else:p.write_text(t)
assert (E/a/'receipt.json').exists(),'Missing receipt; never resubmit'
rc=json.loads((E/a/'receipt.json').read_text());entry={k:v for k,v in rc.items() if k!='deps_fingerprint'};entry['full_receipt']=a+'/receipt.json'
with (E/'NNH_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(entry)+'\n')
print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps']}));sys.exit(rc['exit_status'])
