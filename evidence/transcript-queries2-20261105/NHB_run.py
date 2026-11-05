"""NHB-owned serial client for unchanged S2W launcher; no shared tool edits."""
from pathlib import Path
import subprocess,json,sys,time,hashlib,shlex,lzma,re,os,atexit
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90'
B='/home/dombarker/project-offloads/codex-cx-transcript-queries2-20261105';C='/home/dombarker/project-offloads/codex-cx-transcript-queries-cache-20261104';W='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025';T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
if (E/'NHB_HOLD').exists():sys.exit(75)
guard=E/'NHB_CLIENT_ACTIVE'; fd=os.open(guard,os.O_CREAT|os.O_EXCL|os.O_WRONLY);os.write(fd,str(os.getpid()).encode());os.close(fd);atexit.register(lambda:guard.unlink(missing_ok=True))
a,kind,target=sys.argv[1:];assert kind!='extract' or a=='NHB_E001';assert re.fullmatch('NHB_[LKE][0-9]{3}',a) and 1<=int(a[-3:])<=60 and not (E/a).exists()
def ssh(code,data=None,submitted=False):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,code],input=data,capture_output=True,text=True)
  with (E/'NHB_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=retry,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
  if r.returncode!=255:return r
  if submitted:raise RuntimeError('Submitted; recover read-only, never resubmit')
  if retry<10:time.sleep(60)
 raise RuntimeError('Transport exhausted')
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
  print('reservation wait',flush=True);time.sleep(180);continue
 raise RuntimeError('STOP admission')
files={};sources=[]
if kind=='lean':
 n='NHB_generated/'+target+'.lean';files[n]=(E/(target+'.lean')).read_text();sources=[n]
 command=[T+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NHB_generated','-o','NHB_objects/'+target+'.olean',n]
 if target in ['NHB_Driver','NHB_ProofDriver','NHB_PoolProofDriver','NHB_PoolDriver']:command+=['-c','NHB_native/'+target+'.c']
elif kind=='link':
 sources=['NHB_native/'+target+'.c','NHB_native/NFA_WALKER.c','NHB_native/NFA_MemoryLimit.c']
 command=[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NHB_native/'+target,*sources]
elif kind=='audit':
 sources=['NHB_generated/NHB_ProofDriver.lean','NHB_batch.py','NHB_AUDIT_ROOTS.json','NHB_EXPECTED_IMPORTS.jsonl']+(['NHB_POOL_ROOTS.json'] if target.startswith('pool') else [])
 for n in sources:files[n]=(E/Path(n).name).read_text()
 command=['python3','NHB_batch.py',target]
elif kind=='extract':
 files['NHB_extract.py']=(E/'NHB_extract.py').read_text()
 sources=['NHB_extract.py','NHB_src/Cargo.lock','NHB_src/crates/aspis-core/src/r0_transcript.rs']
 command=['python3','NHB_extract.py',a+'.json']
elif kind=='kani':
 files['NHB_gate.py']=(E/'NHB_gate.py').read_text()
 files['NHB_SOURCE_PINS.json']=(E/'NHB_SOURCE_PINS.json').read_text()
 sources=['NHB_gate.py','NHB_SOURCE_PINS.json']+['NHB_src/'+n for n in json.loads((E/'NHB_SOURCE_PINS.json').read_text()) if n.endswith(('NHB_harness.rs','NHB_pairs.rs','NHB_tail.rs','NHB_absorb.rs','NHB_init.rs','NHB_call.rs','NHB_iterator.rs'))]
 command=['python3','NHB_gate.py',a+'.json']
else:raise ValueError(kind)
config=dict(attempt=a,kind=kind,module=target,sources=sources,command=command,env=dict(LEAN_SYSROOT=T,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',TMPDIR=B+'/NHB_tmp',LEAN_PATH=':'.join([B+'/NHB_objects',C+'/NGQ_final_events_20261105',C+'/NGQ_exports_20261105',C,C+'/NGK_exports_20261105',C+'/NGP_exports_20261105','/home/dombarker/project-offloads/codex-cx-pool-retarget-cache-20261104',W,W+'/objects',T+'/lib/lean'])),timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,deps_fingerprint={},expected_time='Focused import elaboration' if kind=='lean' else 'Optimized linker' if kind=='link' else 'Raw ax2 traversal / coherence scan')
if kind=='kani':
 config['env'].update(CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG='0',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',RUSTFLAGS='-Copt-level=3 -C link-arg=-Wl,--threads=1')
 config['root_package']='aspis-core'
 config['native_command']=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+'/NHB_src/crates/aspis-core/Cargo.toml','--target-dir',B+'/NHB_target','--features','r0','--lib','-j','1','-Z','unstable-options','-Z','function-contracts','-Z','stubbing','--harness-timeout','90s','--exact','--harness',target,'--output-format','terse']
 
 if os.environ.get('NHB_INVERT'):config['env']['RUSTFLAGS']+=' --cfg NHB_invert'
 if os.environ.get('NHB_BYTE_INVERT'):config['env']['RUSTFLAGS']+=' --cfg NHB_reply_corrupt'
 if os.environ.get('NHB_VERIFIER'):
  config['root_package']='aspis-r1-cost-probe'
  i=config['native_command'].index('--manifest-path');config['native_command'][i+1]=B+'/NHB_src/crates/aspis-r1-cost-probe/Cargo.toml'
  i=config['native_command'].index('--features');config['native_command'][i+1]='private-leaf-salts,optimized-terminal,program-build'
 config['expected_time']='Optimized compilation then bounded native control/copy verification; no multiplication'
files[a+'.json']=json.dumps(config)
r=ssh('python3',f'''from pathlib import Path
import json,hashlib,re,shutil
b=Path({B!r});files=json.loads({json.dumps(files)!r})
for n,t in files.items():
 p=b/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
(b/'NHB_native').mkdir(exist_ok=True);(b/'NHB_objects').mkdir(exist_ok=True);(b/'NHB_tmp').mkdir(exist_ok=True)
for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
 p=b/'NHB_native'/n
 if not p.exists():shutil.copy2('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NGJ_native_seed/'+n,p)
x=json.loads((b/{(a+'.json')!r}).read_text());roots=x['env']['LEAN_PATH'].split(':');pins={{}}
modules=['NFA_WALKER','NFA_MemoryLimit','NEP_Planted','NEP_Mutations']
if x['kind']=='lean':modules += re.findall(r'^import ([\\w.]+)',(b/x['sources'][0]).read_text(),re.M)
elif x['kind']=='audit':modules += ['NHB_COMBINED_IMPORT']
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
x['deps_fingerprint']={{'selected_objects':pins,'cache_imports_manifest_sha256':hashlib.sha256((b/'NHB_CACHE_IMPORTS.json.xz').read_bytes()).hexdigest()}}
(b/{(a+'.json')!r}).write_text(json.dumps(x))
''');assert r.returncode==0,r.stderr
r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
r=ssh('python3',f'''from pathlib import Path
import json,hashlib
b=Path({B!r});a={a!r};names=[str(p.relative_to(b)) for p in (b/a).rglob('*') if p.is_file()]+[a+'.json']+([a+'-source-check.json',a+'-graph-check.json',a+'-graph.stderr',a+'-lock-check.json'] if {kind!r}=='kani' else [])
if {kind!r}=='extract':names += [str(p.relative_to(b)) for p in (b/'NHB_extracted').rglob('*') if p.is_file()]+[{(a+'-extraction-pins.json')!r}]
if {kind!r}=='audit':names += [str(p.relative_to(b)) for p in (b/'NHB_audit'/{target!r}).rglob('*') if p.is_file()]+[str(p.relative_to(b)) for modepath in (b/'NHB_audit'/{target!r}).glob('*.json') for row in json.loads(modepath.read_text()).get('results',[]) for p in [b/('NEP_'+modepath.stem+'_'+row['root']+'_REACHABLE.txt')] if p.exists()]+([n for n in ['NHB_LOADED_scan.jsonl','NHB_POOL_LOADED_scan.jsonl'] if (b/n).exists()])
out={{n:(b/n).read_text() for n in names if (b/n).is_file()}}
for name in ['NHB_Driver','NHB_ProofDriver','NHB_PoolProofDriver','NHB_PoolDriver']:
 p=b/'NHB_native'/name
 if p.is_file():out[a+'/'+name+'_BINARY_PIN.json']=json.dumps(dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
print(json.dumps(out))
''');assert r.returncode==0,r.stderr
for n,t in json.loads(r.stdout).items():
 p=E/n;p.parent.mkdir(parents=True,exist_ok=True)
 if n.startswith('NEP_') and n.endswith('_REACHABLE.txt'):
  raw=t.encode();(E/('NHB_'+n+'.sha256')).write_text(hashlib.sha256(raw).hexdigest()+'\n');(E/('NHB_'+n+'.xz')).write_bytes(lzma.compress(raw,preset=6))
 else:p.write_text(t)
assert (E/a/'receipt.json').exists(),'Missing receipt; never resubmit'
rc=json.loads((E/a/'receipt.json').read_text());entry={k:v for k,v in rc.items() if k!='deps_fingerprint'};entry['full_receipt']=a+'/receipt.json'
with (E/'NHB_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(entry)+'\n')
print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}));print((E/a/'stdout.log').read_text()[-3500:]);sys.exit(rc['exit_status'])
