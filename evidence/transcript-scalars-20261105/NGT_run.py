"""NFX-owned serial client for unchanged S2W launcher; no shared tool edits."""
from pathlib import Path
import subprocess,json,sys,time,hashlib,shlex,lzma,re,os,atexit
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90'
B='/home/dombarker/project-offloads/codex-cx-transcript-scalars-20261105';C='/home/dombarker/project-offloads/codex-cx-transcript-scalars-cache-20261104';W='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025';T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
if (E/'NGT_HOLD').exists():sys.exit(75)
guard=E/'NGT_CLIENT_ACTIVE'; fd=os.open(guard,os.O_CREAT|os.O_EXCL|os.O_WRONLY);os.write(fd,str(os.getpid()).encode());os.close(fd);atexit.register(lambda:guard.unlink(missing_ok=True))
a,kind,target=sys.argv[1:];assert re.fullmatch('NGT_[LKE][0-9]{3}',a) and 1<=int(a[-3:])<=(80 if kind=='kani' else 1 if kind=='extract' else 60) and not (E/a).exists()
def ssh(code,data=None,submitted=False):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,code],input=data,capture_output=True,text=True)
  with (E/'NGT_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=retry,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
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
 files['NGT_export.py']=(E/'NGT_export.py').read_text();files['NGT_MODULES.json']=(E/'NGT_MODULES.json').read_text();sources=list(files);command=['python3','NGT_export.py']
elif kind=='metadata':
 files['NGT_capture_graph.py']=(E/'NGT_capture_graph.py').read_text();files['NGT_EXPECTED_GRAPH_HASHES.json']=(E/'NGT_EXPECTED_GRAPH_HASHES.json').read_text();sources=list(files);command=['python3','NGT_capture_graph.py']
elif kind=='extract':
 files['NGT_extract.py']=(E/'NGT_extract.py').read_text();sources=['NGT_extract.py'];command=['python3','NGT_extract.py']
elif kind=='kani':
 files['NGT_gate.py']=(E/'NGT_gate.py').read_text()
 files['NGT_SOURCE_PINS.json']=(E/'NGT_SOURCE_PINS.json').read_text()
 overlay=json.loads((E/'NGT_OVERLAY.json').read_text())
 for dest,src in overlay.items():files['NGT_src/'+dest]=(E/src).read_text()
 sources=list(files)
 command=['python3','NGT_gate.py',a+'.json']
elif kind=='lean':
 n='NGT_generated/'+target+'.lean';files[n]=(E/(target+'.lean')).read_text();sources=[n]
 command=[T+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NGT_generated','-o','NGT_objects/'+target+'.olean',n]
 if target in ['NGT_Driver','NGT_ProofDriver','NGT_PoolProofDriver','NGT_PoolDriver']:command+=['-c','NGT_native/'+target+'.c']
elif kind=='link':
 sources=['NGT_native/'+target+'.c','NGT_native/NFA_WALKER.c','NGT_native/NFA_MemoryLimit.c']
 for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:files['NGT_native/'+n]=(E/'NGT_native'/n).read_text()
 command=[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NGT_native/'+target,*sources]
elif kind=='audit':
 sources=['NGT_generated/NGT_ProofDriver.lean','NGT_generated/NGT_Driver.lean','NGT_batch.py','NGT_AUDIT_ROOTS.json','NGT_EXPECTED_IMPORTS.jsonl']+(['NGT_POOL_ROOTS.json'] if target.startswith('pool') else [])
 for n in sources:files[n]=(E/Path(n).name).read_text()
 command=['python3','NGT_batch.py',target]
else:raise ValueError(kind)
config=dict(attempt=a,kind=kind,module=target,sources=sources,command=command,env=dict(LEAN_SYSROOT=T,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',TMPDIR=B+'/NGT_tmp',LEAN_PATH=':'.join([B+'/NGT_objects',C+'/NGI_exports_20261105',C+'/NFT_exports_20261104',C+'/NFU_exports_20261104',C+'/NFV_final_objects_20261104',C+'/NGE_exports_20261104',C+'/NGF_exports_20261104',C+'/NFY_exports_20261104',C+'/NFY_priority',W,W+'/objects',C+'/NGT_d_fallback/NFQ_exports_20261104',C+'/NGT_d_fallback',C+'/NGT_pool_fallback/NFR_final_objects_20261104',C+'/NGT_pool_fallback/NFO_final_objects_20261104',C+'/NGT_pool_fallback',C+'/NGT_pool_fallback/NEY_final_objects_20261104',C+'/NGT_pool_fallback/NEX_final_objects_20261104',C+'/NGT_pool_fallback/NEQ_final_objects_20261103',C+'/NGT_pool_fallback/NEM_final_objects_20261102',C+'/NGT_pool_fallback/NEU_final_objects_20261104',C,T+'/lib/lean'])),timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,deps_fingerprint={},expected_time='Focused import elaboration' if kind=='lean' else 'Optimized linker' if kind=='link' else 'Raw ax2 traversal / coherence scan')
config['env']['LEAN_PATH']=':'.join(json.loads((E/'NGT_PATHS.json').read_text()))
if kind=='kani':
 config['native_command']=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+'/NGT_src/crates/aspis-r1-cost-probe/Cargo.toml','--target-dir',B+'/NGT_target','--features','private-leaf-salts,optimized-terminal,program-build','--lib','-j','1','-Z','unstable-options','-Z','function-contracts','-Z','stubbing','--harness-timeout','90s','--exact','--harness',target,'--output-format','terse']
 config['env'].update(CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG='0',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',RUSTFLAGS='-Copt-level=3 -C link-arg=-Wl,--threads=1'+(' --cfg NGT_invert' if os.environ.get('NGT_INVERT') else ''))
 if os.environ.get('NGT_BAD_ALLOC'):config['env']['RUSTFLAGS']+=' --cfg NGT_bad_alloc'
 if os.environ.get('NGT_BAD_BOX_VALUE'):config['env']['RUSTFLAGS']+=' --cfg NGT_bad_box_value'
 config['expected_time']='optimized compilation then one native staged cut with local records; no field multiplication'
files[a+'.json']=json.dumps(config)
r=ssh('python3',f'''from pathlib import Path
import json,hashlib,re,shutil
b=Path({B!r});files=json.loads({json.dumps(files)!r})
for n,t in files.items():
 p=b/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
(b/'NGT_native').mkdir(exist_ok=True);(b/'NGT_objects').mkdir(exist_ok=True);(b/'NGT_tmp').mkdir(exist_ok=True)
x=json.loads((b/{(a+'.json')!r}).read_text());roots=x['env']['LEAN_PATH'].split(':');pins={{}}
modules=[]
if x['kind']=='lean':modules += re.findall(r'^import ([\w.]+)',(b/x['sources'][0]).read_text(),re.M)
elif x['kind']=='audit':modules += ['NGT_S_PACKET'] if x['module']=='inventory-s' else ['NGT_D_ONLY'] if x['module']=='inventory-d' else ['NGT_Q_ONLY'] if x['module']=='inventory-q' else ['NGT_POOL_LEGACY_IMPORT'] if {target!r}.startswith('pool') else ['NGT_COMBINED_IMPORT']
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
x['deps_fingerprint']={{'selected_objects':pins,'cache_imports_manifest_sha256':hashlib.sha256((b/'NGT_SEED.json').read_bytes()).hexdigest()}}
(b/{(a+'.json')!r}).write_text(json.dumps(x))
''');assert r.returncode==0,r.stderr
r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
r=ssh('python3',f'''from pathlib import Path
import json,hashlib
b=Path({B!r});a={a!r};names=[str(p.relative_to(b)) for p in (b/a).rglob('*') if p.is_file()]+[a+'.json']
if {kind!r}=='export': names += ['NGT_EXPORT.json','NGT_CLOSURE_PINS.json.sha256']
if {kind!r}=='metadata': names += ['NGT_FULL_GRAPH.json.sha256','NGT_ALL_CRATE_FEATURES.json']
if {kind!r}=='extract': names += ['NGT_EXTRACTION_PINS.json']+([str(p.relative_to(b)) for p in (b/'NGT_extracted').rglob('*') if p.is_file()])+(['NGT_actual.llbc'] if (b/'NGT_actual.llbc').exists() else [])
if {kind!r}=='kani': names += [str(p.relative_to(b)) for p in b.glob(a+'-graph*')]+[str(p.relative_to(b)) for p in b.glob(a+'-source*')]+[str(p.relative_to(b)) for p in b.glob(a+'-lock*')]
if {kind!r}=='audit':names += [str(p.relative_to(b)) for p in (b/'NGT_audit'/{target!r}).rglob('*') if p.is_file()]+[str(p.relative_to(b)) for modepath in (b/'NGT_audit'/{target!r}).glob('*.json') for row in json.loads(modepath.read_text()).get('results',[]) for p in [b/('NEP_'+modepath.stem+'_'+row['root']+'_REACHABLE.txt')] if p.exists()]+([n for n in ['NGT_LOADED_scan.jsonl','NGT_POOL_LOADED_scan.jsonl'] if (b/n).exists()])
out={{n:(b/n).read_text() for n in names}}
for name in ['NGT_Driver','NGT_ProofDriver','NGT_PoolProofDriver','NGT_PoolDriver']:
 p=b/'NGT_native'/name
 if p.is_file():out[a+'/'+name+'_BINARY_PIN.json']=json.dumps(dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
print(json.dumps(out))
''');assert r.returncode==0,r.stderr
for n,t in json.loads(r.stdout).items():
 p=E/n;p.parent.mkdir(parents=True,exist_ok=True)
 if n.startswith('NEP_') and n.endswith('_REACHABLE.txt'):
  raw=t.encode();(E/('NGT_'+n+'.sha256')).write_text(hashlib.sha256(raw).hexdigest()+'\n');(E/('NGT_'+n+'.xz')).write_bytes(lzma.compress(raw,preset=6))
 else:p.write_text(t)
assert (E/a/'receipt.json').exists(),'Missing receipt; never resubmit'
rc=json.loads((E/a/'receipt.json').read_text());entry={k:v for k,v in rc.items() if k!='deps_fingerprint'};entry['full_receipt']=a+'/receipt.json'
with (E/'NGT_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(entry)+'\n')
print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}));print((E/a/'stdout.log').read_text()[-3500:]);sys.exit(rc['exit_status'])
