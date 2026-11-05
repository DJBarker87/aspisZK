"""NHU-owned serial client for unchanged S2W launcher; no shared tool edits."""
from pathlib import Path
import subprocess,json,sys,time,hashlib,shlex,lzma,re,os,atexit
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90'
B='/home/dombarker/project-offloads/codex-cx-verify-observed3-20261106';C='/home/dombarker/project-offloads/codex-cx-prepared-claim-cache-20261104/NHU_seed_20261106';W='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025';T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
if (E/'NHU_HOLD').exists():sys.exit(75)
guard=E/'NHU_CLIENT_ACTIVE'; fd=os.open(guard,os.O_CREAT|os.O_EXCL|os.O_WRONLY);os.write(fd,str(os.getpid()).encode());os.close(fd);atexit.register(lambda:guard.unlink(missing_ok=True))
a,kind,target=sys.argv[1:];assert re.fullmatch('NHU_[LKE][0-9]{3}',a) and 1<=int(a[-3:])<=(80 if kind=='kani' else 1 if kind=='extract' else 90) and not (E/a).exists()
def ssh(code,data=None,submitted=False):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,code],input=data,capture_output=True,text=True)
  with (E/'NHU_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=retry,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
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
  print('reservation wait',flush=True)
  for _ in range(3):time.sleep(60)
  continue
 raise RuntimeError('STOP admission')
files={};sources=[]
if kind=='stage':
 for name in json.loads((E/'NHU_STAGE_INPUTS.json').read_text()):files[name]=(E/name).read_text()
 sources=list(files);command=['python3','NHU_stage_setup.py']
elif kind=='export':
 files['NHU_export.py']=(E/'NHU_export.py').read_text();files['NHU_MODULES.json']=(E/'NHU_MODULES.json').read_text();sources=list(files);command=['python3','NHU_export.py']
elif kind=='metadata':
 files['NHU_capture_graph.py']=(E/'NHU_capture_graph.py').read_text();files['NHU_EXPECTED_GRAPH_HASHES.json']=(E/'NHU_EXPECTED_GRAPH_HASHES.json').read_text();sources=list(files);command=['python3','NHU_capture_graph.py']
elif kind=='extract':
 files['NHU_extract.py']=(E/'NHU_extract.py').read_text();sources=['NHU_extract.py'];command=['python3','NHU_extract.py']
elif kind=='kani':
 files['NHU_gate.py']=(E/'NHU_gate.py').read_text()
 files['NHU_SOURCE_PINS.json']=(E/'NHU_SOURCE_PINS.json').read_text()
 files['NHU_FROZEN_FILE_PINS.json']=(E/'NHU_FROZEN_FILE_PINS.json').read_text()
 overlay=json.loads((E/'NHU_OVERLAY.json').read_text())
 for dest,src in overlay.items():files['NHU_src/'+dest]=(E/src).read_text()
 sources=list(files)
 command=['python3','NHU_gate.py',a+'.json']
elif kind=='lean':
 n='NHU_generated/'+target+'.lean';files[n]=(E/(target+'.lean') if target.startswith('NHU_') else E/('NHU_PREREQ_'+target+'.lean.txt')).read_text();sources=[n]
 command=[T+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NHU_generated','-o','NHU_objects/'+target+'.olean',n]
 if target in ['NHU_Driver','NHU_ProofDriver','NHU_PoolProofDriver','NHU_PoolDriver']:command+=['-c','NHU_native/'+target+'.c']
elif kind=='link':
 sources=['NHU_native/'+target+'.c','NHU_native/NFA_WALKER.c','NHU_native/NFA_MemoryLimit.c']
 for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:files['NHU_native/'+n]=(E/'NHU_native'/n).read_text()
 command=[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NHU_native/'+target,*sources]
elif kind=='audit':
 sources=['NHU_generated/NHU_ProofDriver.lean','NHU_generated/NHU_Driver.lean','NHU_batch.py','NHU_AUDIT_ROOTS.json','NHU_EXPECTED_IMPORTS.jsonl']+(['NHU_POOL_ROOTS.json'] if target.startswith('pool') else [])
 for n in sources:files[n]=(E/Path(n).name).read_text()
 command=['python3','NHU_batch.py',target]
else:raise ValueError(kind)
if kind=='kani' and os.environ.get('NHU_REUSE_INPUTS'):
 prior=E/os.environ['NHU_REUSE_INPUTS']/'sources'
 files={str(p.relative_to(prior)):p.read_text() for p in prior.rglob('*') if p.is_file()}
 sources=list(files)
config=dict(attempt=a,kind=kind,module=target,sources=sources,command=command,env=dict(LEAN_SYSROOT=T,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',TMPDIR=B+'/NHU_tmp',LEAN_PATH=':'.join([B+'/NHU_objects',C+'/NGI_exports_20261105',C+'/NFT_exports_20261104',C+'/NFU_exports_20261104',C+'/NFV_final_objects_20261104',C+'/NGE_exports_20261104',C+'/NGF_exports_20261104',C+'/NFY_exports_20261104',C+'/NFY_priority',W,W+'/objects',C+'/NHU_d_fallback/NFQ_exports_20261104',C+'/NHU_d_fallback',C+'/NHU_pool_fallback/NFR_final_objects_20261104',C+'/NHU_pool_fallback/NFO_final_objects_20261104',C+'/NHU_pool_fallback',C+'/NHU_pool_fallback/NEY_final_objects_20261104',C+'/NHU_pool_fallback/NEX_final_objects_20261104',C+'/NHU_pool_fallback/NEQ_final_objects_20261103',C+'/NHU_pool_fallback/NEM_final_objects_20261102',C+'/NHU_pool_fallback/NEU_final_objects_20261104',C,T+'/lib/lean'])),timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,deps_fingerprint={},expected_time='Focused import elaboration' if kind=='lean' else 'Optimized linker' if kind=='link' else 'Raw ax2 traversal / coherence scan')
config['env']['LEAN_PATH']=':'.join(json.loads((E/'NHU_PATHS.json').read_text()))
if kind=='export':config['expected_time']='copy40 NHU objects and hash final selected coherent closure; no compilation or proof generation'
if kind=='kani':
 config['native_command']=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+'/NHU_src/crates/aspis-r1-cost-probe/Cargo.toml','--target-dir',B+'/NHU_target','--features','private-leaf-salts,optimized-terminal,program-build','--lib','-j','1','-Z','unstable-options','-Z','function-contracts','-Z','stubbing','--harness-timeout','90s','--exact','--harness',target,'--output-format','terse']
 config['env'].update(CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG='0',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',RUSTFLAGS='-Copt-level=3 -C link-arg=-Wl,--threads=1'+(' --cfg NHU_invert' if os.environ.get('NHU_INVERT') else ''))
 if os.environ.get('NHU_BAD_CONTRACT'):
  tag=os.environ['NHU_BAD_CONTRACT'];assert tag in ['i','r','tower','lift'];config['env']['RUSTFLAGS']+=' --cfg NHU_bad_'+tag
 if os.environ.get('NHU_STEP_CASE'):
  tag=os.environ['NHU_STEP_CASE'];assert tag in ['empty','skip','fixed'];config['env']['RUSTFLAGS']+=' --cfg NHU_step_'+tag
 if os.environ.get('NHU_BAD_ALLOC'):config['env']['RUSTFLAGS']+=' --cfg NHU_bad_alloc'
 if os.environ.get('NHU_BAD_BOX_VALUE'):config['env']['RUSTFLAGS']+=' --cfg NHU_bad_box_value'
 if os.environ.get('NHU_PLAYBACK'):
  config['native_command']+=['-Z','concrete-playback','--concrete-playback','print'];ci=config['native_command'];ci[ci.index('--output-format')+1]='regular'
 config['expected_time']='optimized compilation then one native staged cut with local records; no field multiplication'
if kind=='kani' and target.startswith('state_only_hiding::'):
 config['root_package']='aspis-core'
 config['metadata_features']='aspis-r1-cost-probe/private-leaf-salts,aspis-r1-cost-probe/optimized-terminal,aspis-r1-cost-probe/program-build'
 ci=config['native_command'];ci[ci.index('--manifest-path')+1]=B+'/NHU_src/crates/aspis-core/Cargo.toml';ci[ci.index('--features')+1]='r0'
if kind=='kani' and target.startswith('pool_v1::'):
 config['root_package']='aspis-statement'
 features=','.join(next(p['features'] for p in json.loads((E/'NHU_preflight/NHR_GRAPH_CHECK.json').read_text())['features'] if p['name']=='aspis-statement'))
 config['metadata_features']=','.join('aspis-statement/'+f for f in features.split(','))
 ci=config['native_command'];ci[ci.index('--manifest-path')+1]=B+'/NHU_src/crates/aspis-statement/Cargo.toml';ci[ci.index('--features')+1]=features
files[a+'.json']=json.dumps(config)
r=ssh('python3',f'''from pathlib import Path
import json,hashlib,re,shutil
b=Path({B!r});files=json.loads({json.dumps(files)!r})
for n,t in files.items():
 p=b/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
(b/'NHU_native').mkdir(exist_ok=True);(b/'NHU_objects').mkdir(exist_ok=True);(b/'NHU_tmp').mkdir(exist_ok=True)
x=json.loads((b/{(a+'.json')!r}).read_text());roots=x['env']['LEAN_PATH'].split(':');pins={{}}
modules=[]
if x['kind']=='lean':modules += re.findall(r'^import ([\\w.]+)',(b/x['sources'][0]).read_text(),re.M)
elif x['kind']=='audit':modules += ['NHU_S_PACKET'] if x['module']=='inventory-s' else ['NHU_D_ONLY'] if x['module']=='inventory-d' else ['NHU_Q_ONLY'] if x['module']=='inventory-q' else ['NHU_POOL_LEGACY_IMPORT'] if {target!r}.startswith('pool') else ['NHU_COMBINED_IMPORT']
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
x['deps_fingerprint']={{'selected_objects':pins,'cache_imports_manifest_sha256':hashlib.sha256((b/'NHU_SEED.json').read_bytes()).hexdigest()}}
(b/{(a+'.json')!r}).write_text(json.dumps(x))
''');assert r.returncode==0,r.stderr
r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
r=ssh('python3',f'''from pathlib import Path
import json,hashlib
b=Path({B!r});a={a!r};names=[str(p.relative_to(b)) for p in (b/a).rglob('*') if p.is_file()]+[a+'.json']
if {kind!r}=='export': names += ['NHU_EXPORT.json','NHU_CLOSURE_PINS.json.sha256','NHU_CLOSURE_PINS.json']
if {kind!r}=='stage': names += ['NHU_STAGE_REPORT.json','NHU_preflight/NHR_GRAPH_CHECK.json']
if {kind!r}=='metadata': names += ['NHU_FULL_GRAPH.json.sha256','NHU_ALL_CRATE_FEATURES.json']
if {kind!r}=='extract': names += ['NHU_EXTRACTION_PINS.json']+([str(p.relative_to(b)) for p in (b/'NHU_extracted').rglob('*') if p.is_file()])+(['NHU_actual.llbc'] if (b/'NHU_actual.llbc').exists() else [])
if {kind!r}=='kani': names += [str(p.relative_to(b)) for p in b.glob(a+'-graph*')]+[str(p.relative_to(b)) for p in b.glob(a+'-source*')]+[str(p.relative_to(b)) for p in b.glob(a+'-lock*')]
if {kind!r}=='audit':names += [str(p.relative_to(b)) for p in (b/'NHU_audit'/{target!r}).rglob('*') if p.is_file()]+[str(p.relative_to(b)) for modepath in (b/'NHU_audit'/{target!r}).glob('*.json') for row in json.loads(modepath.read_text()).get('results',[]) for p in [b/('NEP_'+modepath.stem+'_'+row['root']+'_REACHABLE.txt')] if p.exists()]+([n for n in ['NHU_LOADED_scan.jsonl','NHU_POOL_LOADED_scan.jsonl'] if (b/n).exists()])
out={{n:(b/n).read_text() for n in names}}
for name in ['NHU_Driver','NHU_ProofDriver','NHU_PoolProofDriver','NHU_PoolDriver']:
 p=b/'NHU_native'/name
 if p.is_file():out[a+'/'+name+'_BINARY_PIN.json']=json.dumps(dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
print(json.dumps(out))
''');assert r.returncode==0,r.stderr
for n,t in json.loads(r.stdout).items():
 p=E/n;p.parent.mkdir(parents=True,exist_ok=True)
 if n.startswith('NEP_') and n.endswith('_REACHABLE.txt'):
  raw=t.encode();(E/('NHU_'+n+'.sha256')).write_text(hashlib.sha256(raw).hexdigest()+'\n');(E/('NHU_'+n+'.xz')).write_bytes(lzma.compress(raw,preset=6))
 else:p.write_text(t)
assert (E/a/'receipt.json').exists(),'Missing receipt; never resubmit'
rc=json.loads((E/a/'receipt.json').read_text());entry={k:v for k,v in rc.items() if k!='deps_fingerprint'};entry['full_receipt']=a+'/receipt.json'
with (E/'NHU_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(entry)+'\n')
if kind=='kani':subprocess.run([sys.executable,str(E/'NHU_pack.py')],check=True)
print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}));print('\n'.join(l for l in (E/a/'stdout.log').read_text().splitlines() if 'VERIFICATION' in l or l.startswith('Failed Checks:')) if kind=='kani' else '\n'.join(l for l in (E/a/'stdout.log').read_text().splitlines() if 'depends on axioms' in l or 'error' in l)[:3500]);sys.exit(rc['exit_status'])
