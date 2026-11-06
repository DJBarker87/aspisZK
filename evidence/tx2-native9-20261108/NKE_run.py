"""NFX-owned serial client for unchanged S2W launcher; no shared tool edits."""
from pathlib import Path
import subprocess,json,sys,time,hashlib,shlex,lzma,re,os,atexit
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90'
B='/home/dombarker/project-offloads/codex-cx-tx2-native9-20261108';C='/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104';W='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025';T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
if (E/'NKE_HOLD').exists():sys.exit(75)
guard=E/'NKE_CLIENT_ACTIVE'; fd=os.open(guard,os.O_CREAT|os.O_EXCL|os.O_WRONLY);os.write(fd,str(os.getpid()).encode());os.close(fd);atexit.register(lambda:guard.unlink(missing_ok=True))
a,kind,target=sys.argv[1:];assert re.fullmatch('NKE_[LKE][0-9]{3}',a) and 1<=int(a[-3:])<=(40 if kind=='kani' else 0 if kind=='extract' else 120) and not (E/a).exists()
def ssh(code,data=None,submitted=False):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,code],input=data,capture_output=True,text=True)
  with (E/'NKE_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=retry,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
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
if kind=='prune':
 files['NKE_prune.py']=(E/'NKE_prune.py').read_text();sources=list(files);command=['python3','NKE_prune.py']
elif kind=='finalcheck':
 for n in ['NKE_final_checks.py','NKE_cleanup.py','NKE_MODULES.json','NKE_SOURCE_PINS.json','NKE_PATHS.json']:files[n]=(E/n).read_text()
 sources=list(files);command=['python3','NKE_final_checks.py']
elif kind=='cleanup':
 files['NKE_cleanup.py']=(E/'NKE_cleanup.py').read_text();sources=list(files);command=['python3','NKE_cleanup.py']
elif kind=='projection':
 for n in ['NKE_projection_check.py','NKE_TREE_CUT.json','NKE_PREFIX_NATIVE_CUT.json','NKE_CTOR_CUT.json']:files[n]=(E/n).read_text()
 sources=list(files);command=['python3','NKE_projection_check.py']
elif kind=='retention':
 files['NKE_retention.py']=(E/'NKE_retention.py').read_text();sources=list(files);command=['python3','NKE_retention.py']
elif kind=='sourcecheck':
 for n in ['NKE_verify_sources.py','NKE_MODULES.json','NKE_SOURCE_PINS.json']:files[n]=(E/n).read_text()
 sources=list(files);command=['python3','NKE_verify_sources.py']
elif kind=='verify':
 files['NKE_verify_exports.py']=(E/'NKE_verify_exports.py').read_text();sources=list(files);command=['python3','NKE_verify_exports.py']
elif kind=='tools':
 files['NKE_tools.py']=(E/'NKE_tools.py').read_text();sources=list(files);command=['python3','NKE_tools.py']
elif kind=='stage':
 files['NKE_stage.py']=(E/'NKE_stage.py').read_text()
 files['NKE_KMX.patch']=Path('evidence/kani-mitig-20261028/KMX_copy_stubs.patch').read_text()
 sources=list(files);command=['python3','NKE_stage.py']
elif kind=='export':
 files['NKE_export.py']=(E/'NKE_export.py').read_text();files['NKE_MODULES.json']=(E/'NKE_MODULES.json').read_text();sources=list(files);command=['python3','NKE_export.py']
elif kind=='metadata':
 files['NKE_capture_graph.py']=(E/'NKE_capture_graph.py').read_text();files['NKE_EXPECTED_GRAPH_HASHES.json']=(E/'NKE_EXPECTED_GRAPH_HASHES.json').read_text();sources=list(files);command=['python3','NKE_capture_graph.py']
elif kind in ['extract','preflight']:
 for n in ['NKE_extract.py','NKE_NHR_stage.py','NKE_EXTRACT_OPACITY.json','NKE_EXTRACT_INPUT_PINS.json']:files[n]=(E/n).read_text()
 sources=list(files);command=['python3','NKE_extract.py']+(['--preflight'] if kind=='preflight' else [])
elif kind=='kani':
 files['NKE_gate.py']=(E/'NKE_gate.py').read_text()
 for n,t in json.loads((E/'NKE_NATIVE_INPUTS.json').read_text()).items():files['NKE_src/'+n]=t
 files['NKE_SOURCE_PINS.json']=(E/'NKE_SOURCE_PINS.json').read_text()
 sources=list(files);command=['python3','NKE_gate.py',a+'.json']
elif kind=='lean':
 n='NKE_generated/'+target+'.lean';files[n]=(E/(target+'.lean')).read_text();sources=[n]
 command=[T+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NKE_generated','-o','NKE_objects/'+target+'.olean',n]
 if target in ['NKE_Driver','NKE_ProofDriver','NKE_PoolProofDriver','NKE_PoolDriver']:command+=['-c','NKE_native/'+target+'.c']
elif kind=='link':
 sources=['NKE_native/'+target+'.c','NKE_native/NFA_WALKER.c','NKE_native/NFA_MemoryLimit.c']
 for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:files['NKE_native/'+n]=(E/'NKE_native'/n).read_text()
 command=[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NKE_native/'+target,*sources]
elif kind=='audit':
 sources=['NKE_generated/NKE_ProofDriver.lean','NKE_generated/NKE_Driver.lean','NKE_batch.py','NKE_AUDIT_ROOTS.json','NKE_EXPECTED_IMPORTS.jsonl']+(['NKE_POOL_ROOTS.json'] if target.startswith('pool') else [])
 for n in sources:files[n]=(E/Path(n).name).read_text()
 command=['python3','NKE_batch.py',target]
else:raise ValueError(kind)
config=dict(attempt=a,kind=kind,module=target,sources=sources,command=command,env=dict(LEAN_SYSROOT=T,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',TMPDIR=B+'/NKE_tmp',LEAN_PATH=':'.join([B+'/NKE_objects',C+'/NGI_exports_20261105',C+'/NFT_exports_20261104',C+'/NFU_exports_20261104',C+'/NFV_final_objects_20261104',C+'/NGE_exports_20261104',C+'/NGF_exports_20261104',C+'/NFY_exports_20261104',C+'/NFY_priority',W,W+'/objects',C+'/NKE_d_fallback/NFQ_exports_20261104',C+'/NKE_d_fallback',C+'/NKE_pool_fallback/NFR_final_objects_20261104',C+'/NKE_pool_fallback/NFO_final_objects_20261104',C+'/NKE_pool_fallback',C+'/NKE_pool_fallback/NEY_final_objects_20261104',C+'/NKE_pool_fallback/NEX_final_objects_20261104',C+'/NKE_pool_fallback/NEQ_final_objects_20261103',C+'/NKE_pool_fallback/NEM_final_objects_20261102',C+'/NKE_pool_fallback/NEU_final_objects_20261104',C,T+'/lib/lean'])),timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,deps_fingerprint={},expected_time='Focused import elaboration' if kind=='lean' else 'Optimized linker' if kind=='link' else 'Raw ax2 traversal / coherence scan')
if kind in ['extract','preflight']:config['expected_time']='optimized dependency compilation, Charon tx2_common with resume transparent, then Aeneas; unchanged private NHR_stage.py'
config['env']['LEAN_PATH']=':'.join(json.loads((E/'NKE_PATHS.json').read_text()))
if kind=='kani':
 config['native_command']=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+'/NKE_src/crates/aspis-r1-cost-probe/Cargo.toml','--target-dir',B+'/NKE_target','--features','private-leaf-salts,optimized-terminal,program-build','--lib','-j','1','-Z','unstable-options','-Z','function-contracts','-Z','stubbing','--harness-timeout','90s','--exact','--harness',target,'--output-format','regular']
 config['env'].update(CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG='0',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',RUSTFLAGS='-Copt-level=3 -C link-arg=-Wl,--threads=1'+(' --cfg NKE_invert' if os.environ.get('NKE_INVERT') else ''))
 if os.environ.get('NKE_BAD_QUERY_WEIGHT_OWNER'):config['env']['RUSTFLAGS']+=' --cfg NKE_bad_query_weight_owner'
 if os.environ.get('NKE_BAD_QUERY_RAW_OWNER'):config['env']['RUSTFLAGS']+=' --cfg NKE_bad_query_raw_owner'
 if os.environ.get('NKE_BAD_POWER'):config['env']['RUSTFLAGS']+=' --cfg NKE_bad_power'
 if os.environ.get('NKE_BAD_NEXT'):config['env']['RUSTFLAGS']+=' --cfg NKE_bad_next'
 if os.environ.get('NKE_BAD_TERMS'):config['env']['RUSTFLAGS']+=' --cfg NKE_bad_terms'
 if os.environ.get('NKE_BAD_RECEIVER_POINTER'):config['env']['RUSTFLAGS']+=' --cfg NKE_bad_receiver_pointer'
 if os.environ.get('NKE_BAD_DESTINATION'):config['env']['RUSTFLAGS']+=' --cfg NKE_bad_destination'
 if os.environ.get('NKE_BAD_RECEIVER'):config['env']['RUSTFLAGS']+=' --cfg NKE_bad_receiver'
 if os.environ.get('NKE_BAD_BACKING'):config['env']['RUSTFLAGS']+=' --cfg NKE_bad_backing'
 if os.environ.get('NKE_BAD_DROP'):config['env']['RUSTFLAGS']+=' --cfg NKE_bad_drop'
 if os.environ.get('NKE_BAD_DECODE_ARG'):config['env']['RUSTFLAGS']+=' --cfg NKE_bad_decode_arg'
 if os.environ.get('NKE_BAD_REPLY'):config['env']['RUSTFLAGS']+=' --cfg NKE_bad_reply'
 if os.environ.get('NKE_BAD_EXPAND'):config['env']['RUSTFLAGS']+=' --cfg NKE_bad_expand'
 if os.environ.get('NKE_BAD_STAGE'):config['env']['RUSTFLAGS']+=' --cfg NKE_bad_stage'
 if os.environ.get('NKE_BAD_VIEW'):config['env']['RUSTFLAGS']+=' --cfg NKE_bad_view'
 if os.environ.get('NKE_BAD_ALLOC'):config['env']['RUSTFLAGS']+=' --cfg NKE_bad_alloc'
 if os.environ.get('NKE_BAD_ERROR'):config['env']['RUSTFLAGS']+=' --cfg NKE_bad_error'
 if os.environ.get('NKE_BAD_BOX_VALUE'):config['env']['RUSTFLAGS']+=' --cfg NKE_bad_box_value'
 if os.environ.get('NKE_CORRUPT_ARGUMENT') is not None:
  z=os.environ['NKE_CORRUPT_ARGUMENT'];assert re.fullmatch('[0-9]',z);config['env']['RUSTFLAGS']+=' --cfg NKE_corrupt'+z
 config['expected_time']='optimized compilation then one native staged cut with local records; no field multiplication'
config['env']['CARGO_TARGET_DIR']=B+'/NKE_target'
files[a+'.json']=json.dumps(config)
r=ssh('python3',f'''from pathlib import Path
import json,hashlib,re,shutil
b=Path({B!r});files=json.loads({json.dumps(files)!r})
for n,t in files.items():
 p=b/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
(b/'NKE_native').mkdir(exist_ok=True);(b/'NKE_objects').mkdir(exist_ok=True);(b/'NKE_tmp').mkdir(exist_ok=True)
x=json.loads((b/{(a+'.json')!r}).read_text());roots=x['env']['LEAN_PATH'].split(':');pins={{}}
modules=[]
if x['kind']=='lean':modules += re.findall(r'^import ([\\w.]+)',(b/x['sources'][0]).read_text(),re.M)
elif x['kind']=='audit':modules += ['NEP_Planted','NEP_Mutations'] if x['module']=='fixtures' else ['NKE_COMBINED_IMPORT']
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
x['deps_fingerprint']={{'selected_objects':pins,'cache_imports_manifest_sha256':hashlib.sha256((b/'NKE_SEED.json').read_bytes()).hexdigest()}}
(b/{(a+'.json')!r}).write_text(json.dumps(x))
''');assert r.returncode==0,r.stderr
r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
r=ssh('python3',f'''from pathlib import Path
import json,hashlib
b=Path({B!r});a={a!r};names=[str(p.relative_to(b)) for p in (b/a).rglob('*') if p.is_file()]+[a+'.json']
if {kind!r}=='prune': names += ['NKE_PRUNE.json']
if {kind!r}=='finalcheck': names += ['NKE_SOURCE_VERIFICATION.json','NKE_TOOL_PINS.json','NKE_EXPORT.json','NKE_CLOSURE_PINS.json.xz','NKE_CLOSURE_PINS.json.sha256','NKE_RETENTION.json','NKE_CLEANUP.json']
if {kind!r}=='cleanup': names += ['NKE_CLEANUP.json']
if {kind!r}=='verify': names += ['NKE_EXPORT_VERIFY.json']
if {kind!r}=='projection': names += ['NKE_PROJECTION_CHECK.json']
if {kind!r}=='retention': names += ['NKE_RETENTION.json','NKE_CLEANUP.json']
if {kind!r}=='sourcecheck': names += ['NKE_SOURCE_VERIFICATION.json']
if {kind!r}=='tools': names += ['NKE_TOOL_PINS.json']
if {kind!r}=='stage': names += ['NKE_STAGE.json','NKE_SOURCE_PINS.json']
if {kind!r}=='export': names += ['NKE_EXPORT.json','NKE_CLOSURE_PINS.json.sha256']
if {kind!r}=='metadata': names += ['NKE_FULL_GRAPH.json.sha256','NKE_ALL_CRATE_FEATURES.json']
if {kind!r}=='extract': names += ['NKE_EXTRACT_PINS.json','NKE_EXTRACT_OUTPUTS.json.xz','NKE_EXTRACT_OUTPUTS.json.sha256']
if {kind!r}=='preflight': names += ['NKE_PREFLIGHT_PINS.json','NKE_PREFLIGHT_OUTPUTS.json.xz','NKE_PREFLIGHT_OUTPUTS.json.sha256']
if {kind!r}=='kani': names += [str(p.relative_to(b)) for p in b.glob(a+'-graph*')]+[str(p.relative_to(b)) for p in b.glob(a+'-source*')]+[str(p.relative_to(b)) for p in b.glob(a+'-lock*')]
if {kind!r}=='audit':names += [str(p.relative_to(b)) for p in (b/'NKE_audit'/{target!r}).rglob('*') if p.is_file()]+[str(p.relative_to(b)) for modepath in (b/'NKE_audit'/{target!r}).glob('*.json') for row in json.loads(modepath.read_text()).get('results',[]) for p in [b/('NEP_'+modepath.stem+'_'+row['root']+'_REACHABLE.txt')] if p.exists()]+([n for n in ['NKE_LOADED_scan.jsonl','NKE_POOL_LOADED_scan.jsonl'] if (b/n).exists()])
out={{}}
for n in names:
 if n.endswith('.xz'):
  import base64
  out[n+'.base64']=base64.b64encode((b/n).read_bytes()).decode()
 else:out[n]=(b/n).read_text()
if {kind!r}=='export':
 import base64
 out['NKE_CLOSURE_PINS.json.xz.base64']=base64.b64encode((b/'NKE_CLOSURE_PINS.json.xz').read_bytes()).decode()
for name in ['NKE_Driver','NKE_ProofDriver','NKE_PoolProofDriver','NKE_PoolDriver']:
 p=b/'NKE_native'/name
 if p.is_file():out[a+'/'+name+'_BINARY_PIN.json']=json.dumps(dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
print(json.dumps(out))
''');assert r.returncode==0,r.stderr
for n,t in json.loads(r.stdout).items():
 p=E/n;p.parent.mkdir(parents=True,exist_ok=True)
 if n.endswith('.base64'):
  import base64
  (E/n.removesuffix('.base64')).write_bytes(base64.b64decode(t))
 elif n.startswith('NEP_') and n.endswith('_REACHABLE.txt'):
  raw=t.encode();(E/('NKE_'+n+'.sha256')).write_text(hashlib.sha256(raw).hexdigest()+'\n');(E/('NKE_'+n+'.xz')).write_bytes(lzma.compress(raw,preset=6))
 else:p.write_text(t)
assert (E/a/'receipt.json').exists(),'Missing receipt; never resubmit'
rc=json.loads((E/a/'receipt.json').read_text());entry={k:v for k,v in rc.items() if k!='deps_fingerprint'};entry['full_receipt']=a+'/receipt.json'
with (E/'NKE_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(entry)+'\n')
summary={k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps']};summary['axiom_lines']=len(rc['print_axioms']) if isinstance(rc['print_axioms'],list) else rc['print_axioms'];print(json.dumps(summary));sys.exit(rc['exit_status'])
