"""NFX-owned serial client for unchanged S2W launcher; no shared tool edits."""
from pathlib import Path
import subprocess,json,sys,time,hashlib,shlex,lzma,re,os,atexit
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90'
B='/home/dombarker/project-offloads/codex-cx-tx2-resume-20261108';C='/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104';W='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025';T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
if (E/'NKK_HOLD').exists():sys.exit(75)
guard=E/'NKK_CLIENT_ACTIVE'; fd=os.open(guard,os.O_CREAT|os.O_EXCL|os.O_WRONLY);os.write(fd,str(os.getpid()).encode());os.close(fd);atexit.register(lambda:guard.unlink(missing_ok=True))
a,kind,target=sys.argv[1:];assert re.fullmatch('NKK_[LKE][0-9]{3}',a) and 1<=int(a[-3:])<=999 and not (E/a).exists()
# Charge real Lean compiler invocations, not numeric labels or support jobs.
prior=[json.loads(p.read_text()) for p in E.glob('NKK_[LKE]*/receipt.json')]
if kind=='lean':assert sum(x['kind']=='lean' for x in prior)<100,'Lean budget exhausted'
if kind=='kani':assert sum(x['kind']=='kani' for x in prior)<50,'Kani budget exhausted'
assert kind!='extract','Extraction budget zero'
def ssh(code,data=None,submitted=False):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,code],input=data,capture_output=True,text=True)
  with (E/'NKK_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=retry,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
  if r.returncode!=255:return r
  if submitted:raise RuntimeError('Submitted; recover read-only, never resubmit')
  if retry<10:time.sleep(60)
 raise RuntimeError('Transport exhausted')
for disk_retry in range(7):
 r=ssh('df -B1 --output=avail /home/dombarker/project-offloads | tail -1')
 free=int(r.stdout.strip()); (E/(a+'-disk.json')).write_text(json.dumps(dict(free_bytes=free,retry=disk_retry)))
 if free>=40_000_000_000:break
 if disk_retry==6:raise RuntimeError('STOP disk below40GB after six waits')
 print('disk wait',flush=True);time.sleep(600)
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
if kind=='prune':
 files['NKK_prune.py']=(E/'NKK_prune.py').read_text();sources=list(files);command=['python3','NKK_prune.py']
elif kind=='finalcheck':
 for n in ['NKK_final_checks.py','NKK_cleanup.py','NKK_MODULES.json','NKK_SOURCE_PINS.json','NKK_PATHS.json']:files[n]=(E/n).read_text()
 sources=list(files);command=['python3','NKK_final_checks.py']
elif kind=='cleanup':
 files['NKK_cleanup.py']=(E/'NKK_cleanup.py').read_text();sources=list(files);command=['python3','NKK_cleanup.py']
elif kind=='projection':
 for n in ['NKK_projection_check.py','NKK_TREE_CUT.json','NKK_PREFIX_NATIVE_CUT.json','NKK_CTOR_CUT.json']:files[n]=(E/n).read_text()
 sources=list(files);command=['python3','NKK_projection_check.py']
elif kind=='retention':
 files['NKK_retention.py']=(E/'NKK_retention.py').read_text();sources=list(files);command=['python3','NKK_retention.py']
elif kind=='sourcecheck':
 for n in ['NKK_verify_sources.py','NKK_MODULES.json','NKK_SOURCE_PINS.json']:files[n]=(E/n).read_text()
 sources=list(files);command=['python3','NKK_verify_sources.py']
elif kind=='verify':
 files['NKK_verify_exports.py']=(E/'NKK_verify_exports.py').read_text();sources=list(files);command=['python3','NKK_verify_exports.py']
elif kind=='tools':
 files['NKK_tools.py']=(E/'NKK_tools.py').read_text();sources=list(files);command=['python3','NKK_tools.py']
elif kind=='stage':
 files['NKK_stage.py']=(E/'NKK_stage.py').read_text()
 files['NKK_KMX.patch']=Path('evidence/kani-mitig-20261028/KMX_copy_stubs.patch').read_text()
 sources=list(files);command=['python3','NKK_stage.py']
elif kind=='export':
 
 for n in ['NKK_export.py','NKK_MODULES.json','NKK_PATHS.json','NKK_retention.py']:files[n]=(E/n).read_text()
 sources=list(files);command=['python3','NKK_export.py']
elif kind=='metadata':
 files['NKK_capture_graph.py']=(E/'NKK_capture_graph.py').read_text();files['NKK_EXPECTED_GRAPH_HASHES.json']=(E/'NKK_EXPECTED_GRAPH_HASHES.json').read_text();sources=list(files);command=['python3','NKK_capture_graph.py']
elif kind in ['extract','preflight']:
 for n in ['NKK_extract.py','NKK_NHR_stage.py','NKK_EXTRACT_OPACITY.json','NKK_EXTRACT_INPUT_PINS.json']:files[n]=(E/n).read_text()
 sources=list(files);command=['python3','NKK_extract.py']+(['--preflight'] if kind=='preflight' else [])
elif kind=='kani':
 files['NKK_gate.py']=(E/'NKK_gate.py').read_text()
 for n,t in json.loads((E/'NKK_NATIVE_INPUTS.json').read_text()).items():files['NKK_src/'+n]=t
 files['NKK_SOURCE_PINS.json']=(E/'NKK_SOURCE_PINS.json').read_text()
 sources=list(files);command=['python3','NKK_gate.py',a+'.json']
elif kind=='lean':
 n='NKK_generated/'+target+'.lean';files[n]=(E/(target+'.lean')).read_text();sources=[n]
 command=[T+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NKK_generated','-o','NKK_objects/'+target+'.olean',n]
 if target in ['NKK_Driver','NKK_ProofDriver','NKK_PoolProofDriver','NKK_PoolDriver']:command+=['-c','NKK_native/'+target+'.c']
elif kind=='link':
 sources=['NKK_native/'+target+'.c','NKK_native/NFA_WALKER.c','NKK_native/NFA_MemoryLimit.c']
 for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:files['NKK_native/'+n]=(E/'NKK_native'/n).read_text()
 command=[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NKK_native/'+target,*sources]
elif kind=='audit':
 sources=['NKK_generated/NKK_ProofDriver.lean','NKK_generated/NKK_Driver.lean','NKK_batch.py','NKK_AUDIT_ROOTS.json','NKK_EXPECTED_IMPORTS.jsonl']+(['NKK_POOL_ROOTS.json'] if target.startswith('pool') else [])
 for n in sources:files[n]=(E/Path(n).name).read_text()
 command=['python3','NKK_batch.py',target]
else:raise ValueError(kind)
config=dict(attempt=a,kind=kind,module=target,sources=sources,command=command,env=dict(LEAN_SYSROOT=T,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',TMPDIR=B+'/NKK_tmp',LEAN_PATH=':'.join([B+'/NKK_objects',C+'/NGI_exports_20261105',C+'/NFT_exports_20261104',C+'/NFU_exports_20261104',C+'/NFV_final_objects_20261104',C+'/NGE_exports_20261104',C+'/NGF_exports_20261104',C+'/NFY_exports_20261104',C+'/NFY_priority',W,W+'/objects',C+'/NKK_d_fallback/NFQ_exports_20261104',C+'/NKK_d_fallback',C+'/NKK_pool_fallback/NFR_final_objects_20261104',C+'/NKK_pool_fallback/NFO_final_objects_20261104',C+'/NKK_pool_fallback',C+'/NKK_pool_fallback/NEY_final_objects_20261104',C+'/NKK_pool_fallback/NEX_final_objects_20261104',C+'/NKK_pool_fallback/NEQ_final_objects_20261103',C+'/NKK_pool_fallback/NEM_final_objects_20261102',C+'/NKK_pool_fallback/NEU_final_objects_20261104',C,T+'/lib/lean'])),timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,deps_fingerprint={},expected_time='Focused import elaboration' if kind=='lean' else 'Optimized linker' if kind=='link' else 'Raw ax2 traversal / coherence scan')
if kind in ['extract','preflight']:config['expected_time']='optimized dependency compilation, Charon tx2_common with resume transparent, then Aeneas; unchanged private NHR_stage.py'
config['env']['LEAN_PATH']=':'.join(json.loads((E/'NKK_PATHS.json').read_text()))
if kind=='kani':
 config['native_command']=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+'/NKK_src/crates/aspis-r1-cost-probe/Cargo.toml','--target-dir',B+'/NKK_target','--features','private-leaf-salts,optimized-terminal,program-build','--lib','-j','1','-Z','unstable-options','-Z','function-contracts','-Z','stubbing','--harness-timeout','90s','--exact','--harness',target,'--output-format','regular']
 config['env'].update(CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG='0',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',RUSTFLAGS='-Copt-level=3 -C link-arg=-Wl,--threads=1'+(' --cfg NKK_invert' if os.environ.get('NKK_INVERT') else ''))
 if os.environ.get('NKK_BAD_QUERY_WEIGHT_OWNER'):config['env']['RUSTFLAGS']+=' --cfg NKK_bad_query_weight_owner'
 if os.environ.get('NKK_BAD_QUERY_RAW_OWNER'):config['env']['RUSTFLAGS']+=' --cfg NKK_bad_query_raw_owner'
 if os.environ.get('NKK_BAD_POWER'):config['env']['RUSTFLAGS']+=' --cfg NKK_bad_power'
 if os.environ.get('NKK_BAD_NEXT'):config['env']['RUSTFLAGS']+=' --cfg NKK_bad_next'
 if os.environ.get('NKK_BAD_TERMS'):config['env']['RUSTFLAGS']+=' --cfg NKK_bad_terms'
 if os.environ.get('NKK_BAD_RECEIVER_POINTER'):config['env']['RUSTFLAGS']+=' --cfg NKK_bad_receiver_pointer'
 if os.environ.get('NKK_BAD_DESTINATION'):config['env']['RUSTFLAGS']+=' --cfg NKK_bad_destination'
 if os.environ.get('NKK_BAD_RECEIVER'):config['env']['RUSTFLAGS']+=' --cfg NKK_bad_receiver'
 if os.environ.get('NKK_BAD_BACKING'):config['env']['RUSTFLAGS']+=' --cfg NKK_bad_backing'
 if os.environ.get('NKK_BAD_DROP'):config['env']['RUSTFLAGS']+=' --cfg NKK_bad_drop'
 if os.environ.get('NKK_BAD_DECODE_ARG'):config['env']['RUSTFLAGS']+=' --cfg NKK_bad_decode_arg'
 if os.environ.get('NKK_BAD_REPLY'):config['env']['RUSTFLAGS']+=' --cfg NKK_bad_reply'
 if os.environ.get('NKK_BAD_EXPAND'):config['env']['RUSTFLAGS']+=' --cfg NKK_bad_expand'
 if os.environ.get('NKK_BAD_STAGE'):config['env']['RUSTFLAGS']+=' --cfg NKK_bad_stage'
 if os.environ.get('NKK_BAD_VIEW'):config['env']['RUSTFLAGS']+=' --cfg NKK_bad_view'
 if os.environ.get('NKK_BAD_ALLOC'):config['env']['RUSTFLAGS']+=' --cfg NKK_bad_alloc'
 if os.environ.get('NKK_BAD_ERROR'):config['env']['RUSTFLAGS']+=' --cfg NKK_bad_error'
 if os.environ.get('NKK_BAD_BOX_VALUE'):config['env']['RUSTFLAGS']+=' --cfg NKK_bad_box_value'
 if os.environ.get('NKK_CORRUPT_ARGUMENT') is not None:
  z=os.environ['NKK_CORRUPT_ARGUMENT'];assert re.fullmatch('[0-9]',z);config['env']['RUSTFLAGS']+=' --cfg NKK_corrupt'+z
 config['expected_time']='optimized compilation then one native staged cut with local records; no field multiplication'
config['env']['CARGO_TARGET_DIR']=B+'/NKK_target'
files[a+'.json']=json.dumps(config)
r=ssh('python3',f'''from pathlib import Path
import json,hashlib,re,shutil
b=Path({B!r});files=json.loads({json.dumps(files)!r})
for n,t in files.items():
 p=b/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
(b/'NKK_native').mkdir(exist_ok=True);(b/'NKK_objects').mkdir(exist_ok=True);(b/'NKK_tmp').mkdir(exist_ok=True)
x=json.loads((b/{(a+'.json')!r}).read_text());roots=x['env']['LEAN_PATH'].split(':');pins={{}}
modules=[]
if x['kind']=='lean':modules += re.findall(r'^import ([\\w.]+)',(b/x['sources'][0]).read_text(),re.M)
elif x['kind']=='audit':modules += ['NEP_Planted','NEP_Mutations'] if x['module']=='fixtures' else ['NKK_COMBINED_IMPORT']
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
x['deps_fingerprint']={{'selected_objects':pins,'cache_imports_manifest_sha256':hashlib.sha256((b/'NKK_SEED.json').read_bytes()).hexdigest()}}
(b/{(a+'.json')!r}).write_text(json.dumps(x))
''');assert r.returncode==0,r.stderr
r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
r=ssh('python3',f'''from pathlib import Path
import json,hashlib
b=Path({B!r});a={a!r};names=[str(p.relative_to(b)) for p in (b/a).rglob('*') if p.is_file()]+[a+'.json']
if {kind!r}=='prune': names += ['NKK_PRUNE.json']
if {kind!r}=='finalcheck': names += ['NKK_SOURCE_VERIFICATION.json','NKK_TOOL_PINS.json','NKK_EXPORT.json','NKK_CLOSURE_PINS.json.xz','NKK_CLOSURE_PINS.json.sha256','NKK_RETENTION.json','NKK_CLEANUP.json']
if {kind!r}=='cleanup': names += ['NKK_CLEANUP.json']
if {kind!r}=='verify': names += ['NKK_EXPORT_VERIFY.json','NKK_FINAL_WALK_MANIFEST.json']
if {kind!r}=='projection': names += ['NKK_PROJECTION_CHECK.json']
if {kind!r}=='retention': names += ['NKK_RETENTION.json','NKK_CLEANUP.json']
if {kind!r}=='sourcecheck': names += ['NKK_SOURCE_VERIFICATION.json']
if {kind!r}=='tools': names += ['NKK_TOOL_PINS.json']
if {kind!r}=='stage': names += ['NKK_STAGE.json']
if {kind!r}=='export': names += ['NKK_EXPORT.json','NKK_CLOSURE_PINS.json.sha256','NKK_RETENTION.json','NKK_CLEANUP.json']
if {kind!r}=='metadata': names += ['NKK_FULL_GRAPH.json.sha256','NKK_ALL_CRATE_FEATURES.json']
if {kind!r}=='extract': names += ['NKK_EXTRACT_PINS.json','NKK_EXTRACT_OUTPUTS.json.xz','NKK_EXTRACT_OUTPUTS.json.sha256']
if {kind!r}=='preflight': names += ['NKK_PREFLIGHT_PINS.json','NKK_PREFLIGHT_OUTPUTS.json.xz','NKK_PREFLIGHT_OUTPUTS.json.sha256']
if {kind!r}=='kani': names += [str(p.relative_to(b)) for p in b.glob(a+'-graph*')]+[str(p.relative_to(b)) for p in b.glob(a+'-source*')]+[str(p.relative_to(b)) for p in b.glob(a+'-lock*')]
if {kind!r}=='audit':names += [str(p.relative_to(b)) for p in (b/'NKK_audit'/{target!r}).rglob('*') if p.is_file()]+[str(p.relative_to(b)) for modepath in (b/'NKK_audit'/{target!r}).glob('*.json') for row in json.loads(modepath.read_text()).get('results',[]) for p in [b/('NEP_'+modepath.stem+'_'+row['root']+'_REACHABLE.txt')] if p.exists()]+([n for n in ['NKK_LOADED_scan.jsonl','NKK_POOL_LOADED_scan.jsonl'] if (b/n).exists()])
out={{}}
for n in names:
 if n.endswith('.xz'):
  import base64
  out[n+'.base64']=base64.b64encode((b/n).read_bytes()).decode()
 else:out[n]=(b/n).read_text()
if {kind!r}=='export':
 import base64
 out['NKK_CLOSURE_PINS.json.xz.base64']=base64.b64encode((b/'NKK_CLOSURE_PINS.json.xz').read_bytes()).decode()
for name in ['NKK_Driver','NKK_ProofDriver','NKK_PoolProofDriver','NKK_PoolDriver']:
 p=b/'NKK_native'/name
 if p.is_file():out[a+'/'+name+'_BINARY_PIN.json']=json.dumps(dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
print(json.dumps(out))
''');assert r.returncode==0,r.stderr
for n,t in json.loads(r.stdout).items():
 p=E/n;p.parent.mkdir(parents=True,exist_ok=True)
 if n.endswith('.base64'):
  import base64
  (E/n.removesuffix('.base64')).write_bytes(base64.b64decode(t))
 elif n.startswith('NEP_') and n.endswith('_REACHABLE.txt'):
  raw=t.encode();(E/('NKK_'+n+'.sha256')).write_text(hashlib.sha256(raw).hexdigest()+'\n');(E/('NKK_'+n+'.xz')).write_bytes(lzma.compress(raw,preset=6))
 else:p.write_text(t)
assert (E/a/'receipt.json').exists(),'Missing receipt; never resubmit'
rc=json.loads((E/a/'receipt.json').read_text());entry={k:v for k,v in rc.items() if k!='deps_fingerprint'};entry['full_receipt']=a+'/receipt.json'
with (E/'NKK_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(entry)+'\n')
summary={k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps']};summary['axiom_lines']=len(rc['print_axioms']) if isinstance(rc['print_axioms'],list) else rc['print_axioms'];print(json.dumps(summary));sys.exit(rc['exit_status'])
