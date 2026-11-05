"""NFX-owned serial client for unchanged S2W launcher; no shared tool edits."""
from pathlib import Path
import subprocess,json,sys,time,hashlib,shlex,lzma,re,os,atexit
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90'
B='/home/dombarker/project-offloads/codex-cx-prepared-claim2-20261105';C='/home/dombarker/project-offloads/codex-cx-prepared-claim-cache-20261104';W='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025';T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
if (E/'NGY_HOLD').exists():sys.exit(75)
guard=E/'NGY_CLIENT_ACTIVE'; fd=os.open(guard,os.O_CREAT|os.O_EXCL|os.O_WRONLY);os.write(fd,str(os.getpid()).encode());os.close(fd);atexit.register(lambda:guard.unlink(missing_ok=True))
a,kind,target=sys.argv[1:];assert re.fullmatch('NGY_[LKE][0-9]{3}',a) and 1<=int(a[-3:])<=(60 if kind=='kani' else 0 if kind=='extract' else 50) and not (E/a).exists()
def ssh(code,data=None,submitted=False):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,code],input=data,capture_output=True,text=True)
  with (E/'NGY_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=retry,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
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
if kind=='export':
 files['NGY_export.py']=(E/'NGY_export.py').read_text();files['NGY_MODULES.json']=(E/'NGY_MODULES.json').read_text();sources=list(files);command=['python3','NGY_export.py']
elif kind=='metadata':
 files['NGY_capture_graph.py']=(E/'NGY_capture_graph.py').read_text();files['NGY_EXPECTED_GRAPH_HASHES.json']=(E/'NGY_EXPECTED_GRAPH_HASHES.json').read_text();sources=list(files);command=['python3','NGY_capture_graph.py']
elif kind=='extract':
 files['NGY_extract.py']=(E/'NGY_extract.py').read_text();sources=['NGY_extract.py'];command=['python3','NGY_extract.py']
elif kind=='kani':
 files['NGY_gate.py']=(E/'NGY_gate.py').read_text()
 files['NGY_SOURCE_PINS.json']=(E/'NGY_SOURCE_PINS.json').read_text()
 payload=json.loads((E/'NGY_PAYLOAD.json').read_text())
 for n,t in payload.items():files['NGY_src/'+n]=t
 sources=list(files)
 command=['python3','NGY_gate.py',a+'.json']
elif kind=='lean':
 n='NGY_generated/'+target+'.lean';files[n]=(E/(target+'.lean')).read_text();sources=[n]
 command=[T+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NGY_generated','-o','NGY_objects/'+target+'.olean',n]
 if target in ['NGY_Driver','NGY_ProofDriver','NGY_PoolProofDriver','NGY_PoolDriver']:command+=['-c','NGY_native/'+target+'.c']
elif kind=='link':
 sources=['NGY_native/'+target+'.c','NGY_native/NFA_WALKER.c','NGY_native/NFA_MemoryLimit.c']
 for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:files['NGY_native/'+n]=(E/'NGY_native'/n).read_text()
 command=[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NGY_native/'+target,*sources]
elif kind=='audit':
 sources=['NGY_generated/NGY_ProofDriver.lean','NGY_generated/NGY_Driver.lean','NGY_batch.py','NGY_AUDIT_ROOTS.json','NGY_EXPECTED_IMPORTS.jsonl']+(['NGY_POOL_ROOTS.json'] if target.startswith('pool') else [])
 for n in sources:files[n]=(E/Path(n).name).read_text()
 command=['python3','NGY_batch.py',target]
else:raise ValueError(kind)
config=dict(attempt=a,kind=kind,module=target,sources=sources,command=command,env=dict(LEAN_SYSROOT=T,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',TMPDIR=B+'/NGY_tmp',LEAN_PATH=':'.join(json.loads((E/'NGY_PATHS.json').read_text()))))
config['source_revision']=subprocess.check_output(['git','rev-parse','HEAD'],cwd=E,text=True).strip()
config['source_tree_dirty']=bool(subprocess.check_output(['git','status','--porcelain'],cwd=E,text=True))
config['frozen_revision']='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
if kind=='kani':
 config['native_command']=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+'/NGY_src/crates/aspis-r1-cost-probe/Cargo.toml','--target-dir',B+'/NGY_target','--features','private-leaf-salts,optimized-terminal,program-build','--lib','-j','1','-Z','unstable-options','-Z','function-contracts','-Z','stubbing','--harness-timeout','90s','--exact','--harness',target,'--output-format','terse']
 config['env'].update(CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG='0',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',RUSTFLAGS='-Copt-level=3 -C link-arg=-Wl,--threads=1'+(' --cfg NGY_corrupt' if os.environ.get('NGY_CORRUPT') else ''))
 if os.environ.get('NGY_BAD_ALLOC'):config['env']['RUSTFLAGS']+=' --cfg NGY_bad_alloc'
 if os.environ.get('NGY_BAD_BOX_VALUE'):config['env']['RUSTFLAGS']+=' --cfg NGY_bad_box_value'
 config['expected_time']='optimized compilation then one native staged cut with local records; no field multiplication'
files[a+'.json']=json.dumps(config)
r=ssh('python3',f'''from pathlib import Path
import json,hashlib,re,shutil
b=Path({B!r});files=json.loads({json.dumps(files)!r})
for n,t in files.items():
 p=b/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
(b/'NGY_native').mkdir(exist_ok=True);(b/'NGY_objects').mkdir(exist_ok=True);(b/'NGY_tmp').mkdir(exist_ok=True)
x=json.loads((b/{(a+'.json')!r}).read_text());roots=x['env']['LEAN_PATH'].split(':');pins={{}}
modules=[]
if x['kind']=='lean':modules += re.findall(r'^import ([\\w.]+)',(b/x['sources'][0]).read_text(),re.M)
elif x['kind']=='audit':modules += ['NGY_S_PACKET'] if x['module']=='inventory-s' else ['NGY_D_ONLY'] if x['module']=='inventory-d' else ['NGY_Q_ONLY'] if x['module']=='inventory-q' else ['NGY_POOL_LEGACY_IMPORT'] if {target!r}.startswith('pool') else ['NGY_COMBINED_IMPORT']
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
x['deps_fingerprint']={{'selected_objects':pins,'cache_imports_manifest_sha256':hashlib.sha256((b/'NGY_SEED.json').read_bytes()).hexdigest()}}
(b/{(a+'.json')!r}).write_text(json.dumps(x))
''');assert r.returncode==0,r.stderr
r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
r=ssh('python3',f'''from pathlib import Path
import json,hashlib
b=Path({B!r});a={a!r};names=[str(p.relative_to(b)) for p in (b/a).rglob('*') if p.is_file()]+[a+'.json']
if {kind!r}=='export': names += ['NGY_EXPORT.json','NGY_CLOSURE_PINS.json.sha256']
if {kind!r}=='metadata': names += ['NGY_FULL_GRAPH.json.sha256','NGY_ALL_CRATE_FEATURES.json']
if {kind!r}=='extract': names += ['NGY_EXTRACTION_PINS.json']+([str(p.relative_to(b)) for p in (b/'NGY_extracted').rglob('*') if p.is_file()])+(['NGY_actual.llbc'] if (b/'NGY_actual.llbc').exists() else [])
if {kind!r}=='kani': names += [a+'-all-crate-features.json']+ [str(p.relative_to(b)) for p in b.glob(a+'-graph*')]+[str(p.relative_to(b)) for p in b.glob(a+'-source*')]+[str(p.relative_to(b)) for p in b.glob(a+'-lock*')]
if {kind!r}=='audit':names += [str(p.relative_to(b)) for p in (b/'NGY_audit'/{target!r}).rglob('*') if p.is_file()]+[str(p.relative_to(b)) for modepath in (b/'NGY_audit'/{target!r}).glob('*.json') for row in json.loads(modepath.read_text()).get('results',[]) for p in [b/('NEP_'+modepath.stem+'_'+row['root']+'_REACHABLE.txt')] if p.exists()]+([n for n in ['NGY_LOADED_scan.jsonl','NGY_POOL_LOADED_scan.jsonl'] if (b/n).exists()])
out={{n:(b/n).read_text() for n in names if (b/n).is_file()}}
for name in ['NGY_Driver','NGY_ProofDriver','NGY_PoolProofDriver','NGY_PoolDriver']:
 p=b/'NGY_native'/name
 if p.is_file():out[a+'/'+name+'_BINARY_PIN.json']=json.dumps(dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
print(json.dumps(out))
''');assert r.returncode==0,r.stderr
for n,t in json.loads(r.stdout).items():
 p=E/n;p.parent.mkdir(parents=True,exist_ok=True)
 if n.startswith('NEP_') and n.endswith('_REACHABLE.txt'):
  raw=t.encode();(E/('NGY_'+n+'.sha256')).write_text(hashlib.sha256(raw).hexdigest()+'\n');(E/('NGY_'+n+'.xz')).write_bytes(lzma.compress(raw,preset=6))
 else:
  if n.startswith('NGY_extracted/') and n.endswith('.lean'):p=Path(str(p)+'.txt')
  p.write_text(t)
assert (E/a/'receipt.json').exists(),'Missing receipt; never resubmit'
rc=json.loads((E/a/'receipt.json').read_text());entry={k:v for k,v in rc.items() if k!='deps_fingerprint'};entry['full_receipt']=a+'/receipt.json'
with (E/'NGY_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(entry)+'\n')
print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps']}|dict(axiom_lines=len(rc['print_axioms']) if isinstance(rc['print_axioms'],list) else 0)));
if rc['exit_status'] and kind!='kani':print((E/a/'stdout.log').read_text()[:4500]);
sys.exit(rc['exit_status'])
