"""NFX-owned serial client for unchanged S2W launcher; no shared tool edits."""
from pathlib import Path
import subprocess,json,sys,time,hashlib,shlex,lzma,re,os,atexit
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90'
B='/home/dombarker/project-offloads/codex-cx-tx2-native8-20261108';C='/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104';W='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025';T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
if (E/'NJU_HOLD').exists():sys.exit(75)
guard=E/'NJU_CLIENT_ACTIVE'; fd=os.open(guard,os.O_CREAT|os.O_EXCL|os.O_WRONLY);os.write(fd,str(os.getpid()).encode());os.close(fd);atexit.register(lambda:guard.unlink(missing_ok=True))
a,kind,target=sys.argv[1:];assert re.fullmatch('NJU_[LKE][0-9]{3}',a) and 1<=int(a[-3:])<=(80 if kind=='kani' else 0 if kind=='extract' else 100) and not (E/a).exists()
def ssh(code,data=None,submitted=False):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,code],input=data,capture_output=True,text=True)
  with (E/'NJU_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=retry,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
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
 files['NJU_prune.py']=(E/'NJU_prune.py').read_text();sources=list(files);command=['python3','NJU_prune.py']
elif kind=='finalcheck':
 for n in ['NJU_final_checks.py','NJU_MODULES.json','NJU_SOURCE_PINS.json','NJU_PATHS.json']:files[n]=(E/n).read_text()
 sources=list(files);command=['python3','NJU_final_checks.py']
elif kind=='cleanup':
 files['NJU_cleanup.py']=(E/'NJU_cleanup.py').read_text();sources=list(files);command=['python3','NJU_cleanup.py']
elif kind=='projection':
 for n in ['NJU_projection_check.py','NJU_TREE_CUT.json','NJU_PREFIX_NATIVE_CUT.json','NJU_CTOR_CUT.json']:files[n]=(E/n).read_text()
 sources=list(files);command=['python3','NJU_projection_check.py']
elif kind=='retention':
 files['NJU_retention.py']=(E/'NJU_retention.py').read_text();sources=list(files);command=['python3','NJU_retention.py']
elif kind=='sourcecheck':
 for n in ['NJU_verify_sources.py','NJU_MODULES.json','NJU_SOURCE_PINS.json']:files[n]=(E/n).read_text()
 sources=list(files);command=['python3','NJU_verify_sources.py']
elif kind=='verify':
 files['NJU_verify_exports.py']=(E/'NJU_verify_exports.py').read_text();sources=list(files);command=['python3','NJU_verify_exports.py']
elif kind=='tools':
 files['NJU_tools.py']=(E/'NJU_tools.py').read_text();sources=list(files);command=['python3','NJU_tools.py']
elif kind=='stage':
 files['NJU_stage.py']=(E/'NJU_stage.py').read_text()
 files['NJU_KMX.patch']=Path('evidence/kani-mitig-20261028/KMX_copy_stubs.patch').read_text()
 sources=list(files);command=['python3','NJU_stage.py']
elif kind=='export':
 files['NJU_export.py']=(E/'NJU_export.py').read_text();files['NJU_MODULES.json']=(E/'NJU_MODULES.json').read_text();sources=list(files);command=['python3','NJU_export.py']
elif kind=='metadata':
 files['NJU_capture_graph.py']=(E/'NJU_capture_graph.py').read_text();files['NJU_EXPECTED_GRAPH_HASHES.json']=(E/'NJU_EXPECTED_GRAPH_HASHES.json').read_text();sources=list(files);command=['python3','NJU_capture_graph.py']
elif kind in ['extract','preflight']:
 for n in ['NJU_extract.py','NJU_NHR_stage.py','NJU_EXTRACT_OPACITY.json','NJU_EXTRACT_INPUT_PINS.json']:files[n]=(E/n).read_text()
 sources=list(files);command=['python3','NJU_extract.py']+(['--preflight'] if kind=='preflight' else [])
elif kind=='kani':
 files['NJU_gate.py']=(E/'NJU_gate.py').read_text()
 for n,t in json.loads((E/'NJU_NATIVE_INPUTS.json').read_text()).items():files['NJU_src/'+n]=t
 files['NJU_SOURCE_PINS.json']=(E/'NJU_SOURCE_PINS.json').read_text()
 sources=list(files);command=['python3','NJU_gate.py',a+'.json']
elif kind=='lean':
 n='NJU_generated/'+target+'.lean';files[n]=(E/(target+'.lean')).read_text();sources=[n]
 command=[T+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NJU_generated','-o','NJU_objects/'+target+'.olean',n]
 if target in ['NJU_Driver','NJU_ProofDriver','NJU_PoolProofDriver','NJU_PoolDriver']:command+=['-c','NJU_native/'+target+'.c']
elif kind=='link':
 sources=['NJU_native/'+target+'.c','NJU_native/NFA_WALKER.c','NJU_native/NFA_MemoryLimit.c']
 for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:files['NJU_native/'+n]=(E/'NJU_native'/n).read_text()
 command=[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NJU_native/'+target,*sources]
elif kind=='audit':
 sources=['NJU_generated/NJU_ProofDriver.lean','NJU_generated/NJU_Driver.lean','NJU_batch.py','NJU_AUDIT_ROOTS.json','NJU_EXPECTED_IMPORTS.jsonl']+(['NJU_POOL_ROOTS.json'] if target.startswith('pool') else [])
 for n in sources:files[n]=(E/Path(n).name).read_text()
 command=['python3','NJU_batch.py',target]
else:raise ValueError(kind)
config=dict(attempt=a,kind=kind,module=target,sources=sources,command=command,env=dict(LEAN_SYSROOT=T,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',TMPDIR=B+'/NJU_tmp',LEAN_PATH=':'.join([B+'/NJU_objects',C+'/NGI_exports_20261105',C+'/NFT_exports_20261104',C+'/NFU_exports_20261104',C+'/NFV_final_objects_20261104',C+'/NGE_exports_20261104',C+'/NGF_exports_20261104',C+'/NFY_exports_20261104',C+'/NFY_priority',W,W+'/objects',C+'/NJU_d_fallback/NFQ_exports_20261104',C+'/NJU_d_fallback',C+'/NJU_pool_fallback/NFR_final_objects_20261104',C+'/NJU_pool_fallback/NFO_final_objects_20261104',C+'/NJU_pool_fallback',C+'/NJU_pool_fallback/NEY_final_objects_20261104',C+'/NJU_pool_fallback/NEX_final_objects_20261104',C+'/NJU_pool_fallback/NEQ_final_objects_20261103',C+'/NJU_pool_fallback/NEM_final_objects_20261102',C+'/NJU_pool_fallback/NEU_final_objects_20261104',C,T+'/lib/lean'])),timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,deps_fingerprint={},expected_time='Focused import elaboration' if kind=='lean' else 'Optimized linker' if kind=='link' else 'Raw ax2 traversal / coherence scan')
if kind in ['extract','preflight']:config['expected_time']='optimized dependency compilation, Charon tx2_common with resume transparent, then Aeneas; unchanged private NHR_stage.py'
config['env']['LEAN_PATH']=':'.join(json.loads((E/'NJU_PATHS.json').read_text()))
if kind=='kani':
 config['native_command']=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+'/NJU_src/crates/aspis-r1-cost-probe/Cargo.toml','--target-dir',B+'/NJU_target','--features','private-leaf-salts,optimized-terminal,program-build','--lib','-j','1','-Z','unstable-options','-Z','function-contracts','-Z','stubbing','--harness-timeout','90s','--exact','--harness',target,'--output-format','terse']
 config['env'].update(CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG='0',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',RUSTFLAGS='-Copt-level=3 -C link-arg=-Wl,--threads=1'+(' --cfg NJU_invert' if os.environ.get('NJU_INVERT') else ''))
 if os.environ.get('NJU_BAD_QUERY_WEIGHT_OWNER'):config['env']['RUSTFLAGS']+=' --cfg NJU_bad_query_weight_owner'
 if os.environ.get('NJU_BAD_QUERY_RAW_OWNER'):config['env']['RUSTFLAGS']+=' --cfg NJU_bad_query_raw_owner'
 if os.environ.get('NJU_BAD_POWER'):config['env']['RUSTFLAGS']+=' --cfg NJU_bad_power'
 if os.environ.get('NJU_BAD_NEXT'):config['env']['RUSTFLAGS']+=' --cfg NJU_bad_next'
 if os.environ.get('NJU_BAD_TERMS'):config['env']['RUSTFLAGS']+=' --cfg NJU_bad_terms'
 if os.environ.get('NJU_BAD_RECEIVER_POINTER'):config['env']['RUSTFLAGS']+=' --cfg NJU_bad_receiver_pointer'
 if os.environ.get('NJU_BAD_DESTINATION'):config['env']['RUSTFLAGS']+=' --cfg NJU_bad_destination'
 if os.environ.get('NJU_BAD_RECEIVER'):config['env']['RUSTFLAGS']+=' --cfg NJU_bad_receiver'
 if os.environ.get('NJU_BAD_BACKING'):config['env']['RUSTFLAGS']+=' --cfg NJU_bad_backing'
 if os.environ.get('NJU_BAD_DROP'):config['env']['RUSTFLAGS']+=' --cfg NJU_bad_drop'
 if os.environ.get('NJU_BAD_DECODE_ARG'):config['env']['RUSTFLAGS']+=' --cfg NJU_bad_decode_arg'
 if os.environ.get('NJU_BAD_REPLY'):config['env']['RUSTFLAGS']+=' --cfg NJU_bad_reply'
 if os.environ.get('NJU_BAD_EXPAND'):config['env']['RUSTFLAGS']+=' --cfg NJU_bad_expand'
 if os.environ.get('NJU_BAD_STAGE'):config['env']['RUSTFLAGS']+=' --cfg NJU_bad_stage'
 if os.environ.get('NJU_BAD_VIEW'):config['env']['RUSTFLAGS']+=' --cfg NJU_bad_view'
 if os.environ.get('NJU_BAD_ALLOC'):config['env']['RUSTFLAGS']+=' --cfg NJU_bad_alloc'
 if os.environ.get('NJU_BAD_ERROR'):config['env']['RUSTFLAGS']+=' --cfg NJU_bad_error'
 if os.environ.get('NJU_BAD_BOX_VALUE'):config['env']['RUSTFLAGS']+=' --cfg NJU_bad_box_value'
 if os.environ.get('NJU_CORRUPT_ARGUMENT') is not None:
  z=os.environ['NJU_CORRUPT_ARGUMENT'];assert re.fullmatch('[0-9]',z);config['env']['RUSTFLAGS']+=' --cfg NJU_corrupt'+z
 config['expected_time']='optimized compilation then one native staged cut with local records; no field multiplication'
config['env']['CARGO_TARGET_DIR']=B+'/NJU_target'
files[a+'.json']=json.dumps(config)
r=ssh('python3',f'''from pathlib import Path
import json,hashlib,re,shutil
b=Path({B!r});files=json.loads({json.dumps(files)!r})
for n,t in files.items():
 p=b/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
(b/'NJU_native').mkdir(exist_ok=True);(b/'NJU_objects').mkdir(exist_ok=True);(b/'NJU_tmp').mkdir(exist_ok=True)
x=json.loads((b/{(a+'.json')!r}).read_text());roots=x['env']['LEAN_PATH'].split(':');pins={{}}
modules=[]
if x['kind']=='lean':modules += re.findall(r'^import ([\\w.]+)',(b/x['sources'][0]).read_text(),re.M)
elif x['kind']=='audit':modules += ['NEP_Planted','NEP_Mutations'] if x['module']=='fixtures' else ['NJU_COMBINED_IMPORT']
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
x['deps_fingerprint']={{'selected_objects':pins,'cache_imports_manifest_sha256':hashlib.sha256((b/'NJU_SEED.json').read_bytes()).hexdigest()}}
(b/{(a+'.json')!r}).write_text(json.dumps(x))
''');assert r.returncode==0,r.stderr
r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
r=ssh('python3',f'''from pathlib import Path
import json,hashlib
b=Path({B!r});a={a!r};names=[str(p.relative_to(b)) for p in (b/a).rglob('*') if p.is_file()]+[a+'.json']
if {kind!r}=='prune': names += ['NJU_PRUNE.json']
if {kind!r}=='finalcheck': names += ['NJU_SOURCE_VERIFICATION.json','NJU_TOOL_PINS.json','NJU_EXPORT.json','NJU_CLOSURE_PINS.json.xz','NJU_CLOSURE_PINS.json.sha256','NJU_RETENTION.json']
if {kind!r}=='cleanup': names += ['NJU_CLEANUP.json']
if {kind!r}=='projection': names += ['NJU_PROJECTION_CHECK.json']
if {kind!r}=='retention': names += ['NJU_RETENTION.json']
if {kind!r}=='sourcecheck': names += ['NJU_SOURCE_VERIFICATION.json']
if {kind!r}=='verify': names += ['NJU_CACHE_VERIFICATION.json']
if {kind!r}=='tools': names += ['NJU_TOOL_PINS.json']
if {kind!r}=='stage': names += ['NJU_STAGE.json']
if {kind!r}=='export': names += ['NJU_EXPORT.json','NJU_CLOSURE_PINS.json.sha256']
if {kind!r}=='metadata': names += ['NJU_FULL_GRAPH.json.sha256','NJU_ALL_CRATE_FEATURES.json']
if {kind!r}=='extract': names += ['NJU_EXTRACT_PINS.json','NJU_EXTRACT_OUTPUTS.json.xz','NJU_EXTRACT_OUTPUTS.json.sha256']
if {kind!r}=='preflight': names += ['NJU_PREFLIGHT_PINS.json','NJU_PREFLIGHT_OUTPUTS.json.xz','NJU_PREFLIGHT_OUTPUTS.json.sha256']
if {kind!r}=='kani': names += [str(p.relative_to(b)) for p in b.glob(a+'-graph*')]+[str(p.relative_to(b)) for p in b.glob(a+'-source*')]+[str(p.relative_to(b)) for p in b.glob(a+'-lock*')]
if {kind!r}=='audit':names += [str(p.relative_to(b)) for p in (b/'NJU_audit'/{target!r}).rglob('*') if p.is_file()]+[str(p.relative_to(b)) for modepath in (b/'NJU_audit'/{target!r}).glob('*.json') for row in json.loads(modepath.read_text()).get('results',[]) for p in [b/('NEP_'+modepath.stem+'_'+row['root']+'_REACHABLE.txt')] if p.exists()]+([n for n in ['NJU_LOADED_scan.jsonl','NJU_POOL_LOADED_scan.jsonl'] if (b/n).exists()])
out={{}}
for n in names:
 if n.endswith('.xz'):
  import base64
  out[n+'.base64']=base64.b64encode((b/n).read_bytes()).decode()
 else:out[n]=(b/n).read_text()
if {kind!r}=='export':
 import base64
 out['NJU_CLOSURE_PINS.json.xz.base64']=base64.b64encode((b/'NJU_CLOSURE_PINS.json.xz').read_bytes()).decode()
for name in ['NJU_Driver','NJU_ProofDriver','NJU_PoolProofDriver','NJU_PoolDriver']:
 p=b/'NJU_native'/name
 if p.is_file():out[a+'/'+name+'_BINARY_PIN.json']=json.dumps(dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
print(json.dumps(out))
''');assert r.returncode==0,r.stderr
for n,t in json.loads(r.stdout).items():
 p=E/n;p.parent.mkdir(parents=True,exist_ok=True)
 if n.endswith('.base64'):
  import base64
  (E/n.removesuffix('.base64')).write_bytes(base64.b64decode(t))
 elif n.startswith('NEP_') and n.endswith('_REACHABLE.txt'):
  raw=t.encode();(E/('NJU_'+n+'.sha256')).write_text(hashlib.sha256(raw).hexdigest()+'\n');(E/('NJU_'+n+'.xz')).write_bytes(lzma.compress(raw,preset=6))
 else:p.write_text(t)
assert (E/a/'receipt.json').exists(),'Missing receipt; never resubmit'
rc=json.loads((E/a/'receipt.json').read_text());entry={k:v for k,v in rc.items() if k!='deps_fingerprint'};entry['full_receipt']=a+'/receipt.json'
with (E/'NJU_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(entry)+'\n')
summary={k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps']};summary['axiom_lines']=len(rc['print_axioms']) if isinstance(rc['print_axioms'],list) else rc['print_axioms'];print(json.dumps(summary));sys.exit(rc['exit_status'])
