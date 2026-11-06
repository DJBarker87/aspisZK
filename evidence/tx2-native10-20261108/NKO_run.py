"""NFX-owned serial client for unchanged S2W launcher; no shared tool edits."""
from pathlib import Path
import subprocess,json,sys,time,hashlib,shlex,lzma,re,os,atexit
from NKO_read import read_text
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90'
B='/home/dombarker/project-offloads/codex-cx-tx2-native10-20261108';C='/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104';W='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025';T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
if (E/'NKO_HOLD').exists():sys.exit(75)
guard=E/'NKO_CLIENT_ACTIVE'; fd=os.open(guard,os.O_CREAT|os.O_EXCL|os.O_WRONLY);os.write(fd,str(os.getpid()).encode());os.close(fd);atexit.register(lambda:guard.unlink(missing_ok=True))
a,kind,target=sys.argv[1:];assert re.fullmatch('NKO_[LKE][0-9]{3}',a) and 1<=int(a[-3:])<=(60 if kind=='kani' else 0 if kind=='extract' else 120) and not (E/a).exists()
if kind=='kani':
 completed=[json.loads(l) for l in (E/'NKO_ATTEMPTS.jsonl').read_text().splitlines()]
 assert sum(r['kind']=='kani' for r in completed)<60,'Kani process budget exhausted'
 # K001 and K018 are retained pre-launch failures, not native invocations.


def ssh(code,data=None,submitted=False):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,code],input=data,capture_output=True,text=True)
  with (E/'NKO_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=retry,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
  if r.returncode!=255:return r
  if submitted:raise RuntimeError('Submitted; recover read-only, never resubmit')
  if retry<10:time.sleep(60)
 raise RuntimeError('Transport exhausted')
disk=ssh("python3 -c 'import shutil,json;print(json.dumps(dict(free=shutil.disk_usage(\"/home/dombarker/project-offloads\").free)))'")
assert disk.returncode==0 and json.loads(disk.stdout)['free']>=40_000_000_000,'DISK WAIT required'
(E/(a+'-disk.json')).write_text(disk.stdout)
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
 files['NKO_prune.py']=(E/'NKO_prune.py').read_text();sources=list(files);command=['python3','NKO_prune.py']
elif kind=='finalcheck':
 for n in ['NKO_final_checks.py','NKO_cleanup.py','NKO_MODULES.json','NKO_SOURCE_PINS.json','NKO_PATHS.json']:files[n]=(E/n).read_text()
 sources=list(files);command=['python3','NKO_final_checks.py']
elif kind=='cleanup':
 files['NKO_cleanup.py']=(E/'NKO_cleanup.py').read_text();sources=list(files);command=['python3','NKO_cleanup.py']
elif kind=='projection':
 for n in ['NKO_projection_check.py','NKO_TREE_CUT.json','NKO_PREFIX_NATIVE_CUT.json','NKO_CTOR_CUT.json']:files[n]=(E/n).read_text()
 sources=list(files);command=['python3','NKO_projection_check.py']
elif kind=='retention':
 files['NKO_retention.py']=(E/'NKO_retention.py').read_text();sources=list(files);command=['python3','NKO_retention.py']
elif kind=='sourcecheck':
 for n in ['NKO_verify_sources.py','NKO_MODULES.json','NKO_SOURCE_PINS.json']:files[n]=(E/n).read_text()
 sources=list(files);command=['python3','NKO_verify_sources.py']
elif kind=='verify':
 files['NKO_verify_exports.py']=(E/'NKO_verify_exports.py').read_text();sources=list(files);command=['python3','NKO_verify_exports.py']
elif kind=='tools':
 files['NKO_tools.py']=(E/'NKO_tools.py').read_text();sources=list(files);command=['python3','NKO_tools.py']
elif kind=='stage':
 files['NKO_stage.py']=(E/'NKO_stage.py').read_text()
 files['NKO_KMX.patch']=Path('evidence/kani-mitig-20261028/KMX_copy_stubs.patch').read_text()
 sources=list(files);command=['python3','NKO_stage.py']
elif kind=='export':
 files['NKO_export.py']=(E/'NKO_export.py').read_text();files['NKO_MODULES.json']=(E/'NKO_MODULES.json').read_text();sources=list(files);command=['python3','NKO_export.py']
elif kind=='metadata':
 files['NKO_capture_graph.py']=(E/'NKO_capture_graph.py').read_text();files['NKO_EXPECTED_GRAPH_HASHES.json']=(E/'NKO_EXPECTED_GRAPH_HASHES.json').read_text();sources=list(files);command=['python3','NKO_capture_graph.py']
elif kind=='review':
 for n in ['NKO_review.py','NKO_HARNESS.patch','NKO_NATIVE_PAIRS.json','NKO_OCCURRENCES.json','NKO_CLOSED.json','NKO_LEDGER_DELTA.json','NKO_AUDIT_ROOTS.json']:files[n]=(E/n).read_text()
 sources=list(files);command=['python3','NKO_review.py',target]
elif kind in ['extract','preflight']:
 for n in ['NKO_extract.py','NKO_NHR_stage.py','NKO_EXTRACT_OPACITY.json','NKO_EXTRACT_INPUT_PINS.json']:files[n]=(E/n).read_text()
 sources=list(files);command=['python3','NKO_extract.py']+(['--preflight'] if kind=='preflight' else [])
elif kind=='kani':
 files['NKO_gate.py']=(E/'NKO_gate.py').read_text()
 for n,t in json.loads(read_text(E/'NKO_NATIVE_INPUTS.json')).items():files['NKO_src/'+n]=t
 files['NKO_SOURCE_PINS.json']=(E/'NKO_SOURCE_PINS.json').read_text()
 sources=list(files);command=['python3','NKO_gate.py',a+'.json']
elif kind=='lean':
 n='NKO_generated/'+target+'.lean';files[n]=(E/(target+'.lean')).read_text();sources=[n]
 command=[T+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NKO_generated','-o','NKO_objects/'+target+'.olean',n]
 if target in ['NKO_Driver','NKO_ProofDriver','NKO_PoolProofDriver','NKO_PoolDriver']:command+=['-c','NKO_native/'+target+'.c']
elif kind=='link':
 sources=['NKO_native/'+target+'.c','NKO_native/NFA_WALKER.c','NKO_native/NFA_MemoryLimit.c']
 for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:files['NKO_native/'+n]=(E/'NKO_native'/n).read_text()
 command=[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NKO_native/'+target,*sources]
elif kind=='audit':
 sources=['NKO_generated/NKO_ProofDriver.lean','NKO_generated/NKO_Driver.lean','NKO_batch.py','NKO_AUDIT_ROOTS.json','NKO_EXPECTED_IMPORTS.jsonl']+(['NKO_POOL_ROOTS.json'] if target.startswith('pool') else [])
 for n in sources:files[n]=read_text(E/Path(n).name)
 command=['python3','NKO_batch.py',target]
else:raise ValueError(kind)
config=dict(attempt=a,kind=kind,module=target,sources=sources,command=command,env=dict(LEAN_SYSROOT=T,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',TMPDIR=B+'/NKO_tmp',LEAN_PATH=':'.join([B+'/NKO_objects',C+'/NGI_exports_20261105',C+'/NFT_exports_20261104',C+'/NFU_exports_20261104',C+'/NFV_final_objects_20261104',C+'/NGE_exports_20261104',C+'/NGF_exports_20261104',C+'/NFY_exports_20261104',C+'/NFY_priority',W,W+'/objects',C+'/NKO_d_fallback/NFQ_exports_20261104',C+'/NKO_d_fallback',C+'/NKO_pool_fallback/NFR_final_objects_20261104',C+'/NKO_pool_fallback/NFO_final_objects_20261104',C+'/NKO_pool_fallback',C+'/NKO_pool_fallback/NEY_final_objects_20261104',C+'/NKO_pool_fallback/NEX_final_objects_20261104',C+'/NKO_pool_fallback/NEQ_final_objects_20261103',C+'/NKO_pool_fallback/NEM_final_objects_20261102',C+'/NKO_pool_fallback/NEU_final_objects_20261104',C,T+'/lib/lean'])),timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,deps_fingerprint={},expected_time='Focused import elaboration' if kind=='lean' else 'Optimized linker' if kind=='link' else 'Raw ax2 traversal / coherence scan')
if kind in ['extract','preflight']:config['expected_time']='optimized dependency compilation, Charon tx2_common with resume transparent, then Aeneas; unchanged private NHR_stage.py'
config['env']['LEAN_PATH']=':'.join(json.loads((E/'NKO_PATHS.json').read_text()))
if kind=='kani':
 config['native_command']=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+'/NKO_src/crates/aspis-r1-cost-probe/Cargo.toml','--target-dir',B+'/NKO_target','--features','private-leaf-salts,optimized-terminal,program-build','--lib','-j','1','-Z','unstable-options','-Z','function-contracts','-Z','stubbing','--harness-timeout','90s','--exact','--harness',target,'--output-format','regular']
 config['env'].update(CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG='0',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',RUSTFLAGS='-Copt-level=3 -C link-arg=-Wl,--threads=1'+(' --cfg NKO_invert' if os.environ.get('NKO_INVERT') else ''))
 if os.environ.get('NKO_SHORT_CONTROL'):config['env']['RUSTFLAGS']+=' --cfg NKO_short_control'
 if os.environ.get('NKO_BAD_QUERY_WEIGHT_OWNER'):config['env']['RUSTFLAGS']+=' --cfg NKO_bad_query_weight_owner'
 if os.environ.get('NKO_BAD_QUERY_RAW_OWNER'):config['env']['RUSTFLAGS']+=' --cfg NKO_bad_query_raw_owner'
 if os.environ.get('NKO_BAD_POWER'):config['env']['RUSTFLAGS']+=' --cfg NKO_bad_power'
 if os.environ.get('NKO_BAD_NEXT'):config['env']['RUSTFLAGS']+=' --cfg NKO_bad_next'
 if os.environ.get('NKO_BAD_TERMS'):config['env']['RUSTFLAGS']+=' --cfg NKO_bad_terms'
 if os.environ.get('NKO_BAD_RECEIVER_POINTER'):config['env']['RUSTFLAGS']+=' --cfg NKO_bad_receiver_pointer'
 if os.environ.get('NKO_BAD_DESTINATION'):config['env']['RUSTFLAGS']+=' --cfg NKO_bad_destination'
 if os.environ.get('NKO_BAD_RECEIVER'):config['env']['RUSTFLAGS']+=' --cfg NKO_bad_receiver'
 if os.environ.get('NKO_BAD_BACKING'):config['env']['RUSTFLAGS']+=' --cfg NKO_bad_backing'
 if os.environ.get('NKO_BAD_DROP'):config['env']['RUSTFLAGS']+=' --cfg NKO_bad_drop'
 if os.environ.get('NKO_BAD_DECODE_ARG'):config['env']['RUSTFLAGS']+=' --cfg NKO_bad_decode_arg'
 if os.environ.get('NKO_BAD_REPLY'):config['env']['RUSTFLAGS']+=' --cfg NKO_bad_reply'
 if os.environ.get('NKO_BAD_EXPAND'):config['env']['RUSTFLAGS']+=' --cfg NKO_bad_expand'
 if os.environ.get('NKO_BAD_STAGE'):config['env']['RUSTFLAGS']+=' --cfg NKO_bad_stage'
 if os.environ.get('NKO_BAD_VIEW'):config['env']['RUSTFLAGS']+=' --cfg NKO_bad_view'
 if os.environ.get('NKO_BAD_ALLOC'):config['env']['RUSTFLAGS']+=' --cfg NKO_bad_alloc'
 if os.environ.get('NKO_BAD_ERROR'):config['env']['RUSTFLAGS']+=' --cfg NKO_bad_error'
 if os.environ.get('NKO_BAD_BOX_VALUE'):config['env']['RUSTFLAGS']+=' --cfg NKO_bad_box_value'
 if os.environ.get('NKO_CORRUPT_ARGUMENT') is not None:
  z=os.environ['NKO_CORRUPT_ARGUMENT'];assert re.fullmatch('[0-9]',z);config['env']['RUSTFLAGS']+=' --cfg NKO_corrupt'+z
 config['expected_time']='optimized compilation then one native staged cut with local records; no field multiplication'
config['env']['CARGO_TARGET_DIR']=B+'/NKO_target'
files[a+'.json']=json.dumps(config)
r=ssh('python3',f'''from pathlib import Path
import json,hashlib,re,shutil
b=Path({B!r});files=json.loads({json.dumps(files)!r})
for n,t in files.items():
 p=b/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
(b/'NKO_native').mkdir(exist_ok=True);(b/'NKO_objects').mkdir(exist_ok=True);(b/'NKO_tmp').mkdir(exist_ok=True)
x=json.loads((b/{(a+'.json')!r}).read_text());roots=x['env']['LEAN_PATH'].split(':');pins={{}}
modules=[]
if x['kind']=='lean':modules += re.findall(r'^import ([\\w.]+)',(b/x['sources'][0]).read_text(),re.M)
elif x['kind']=='audit':modules += ['NEP_Planted','NEP_Mutations'] if x['module']=='fixtures' else ['NKO_COMBINED_IMPORT']
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
x['deps_fingerprint']={{'selected_objects':pins,'cache_imports_manifest_sha256':hashlib.sha256((b/'NKO_SEED.json').read_bytes()).hexdigest()}}
(b/{(a+'.json')!r}).write_text(json.dumps(x))
''');assert r.returncode==0,r.stderr
r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
r=ssh('python3',f'''from pathlib import Path
import json,hashlib
b=Path({B!r});a={a!r};names=[str(p.relative_to(b)) for p in (b/a).rglob('*') if p.is_file()]+[a+'.json']
if {kind!r}=='prune': names += ['NKO_PRUNE.json']
if {kind!r}=='finalcheck': names += ['NKO_SOURCE_VERIFICATION.json','NKO_TOOL_PINS.json','NKO_EXPORT.json','NKO_CLOSURE_PINS.json.xz','NKO_CLOSURE_PINS.json.sha256','NKO_RETENTION.json','NKO_CLEANUP.json']
if {kind!r}=='cleanup': names += ['NKO_CLEANUP.json']
if {kind!r}=='review': names += ['NKO_REVIEW_'+{target!r}+'.json']
if {kind!r}=='verify': names += ['NKO_EXPORT_VERIFY.json']
if {kind!r}=='projection': names += ['NKO_PROJECTION_CHECK.json']
if {kind!r}=='retention': names += ['NKO_RETENTION.json','NKO_CLEANUP.json']
if {kind!r}=='sourcecheck': names += ['NKO_SOURCE_VERIFICATION.json']
if {kind!r}=='tools': names += ['NKO_TOOL_PINS.json']
if {kind!r}=='stage': names += ['NKO_STAGE.json','NKO_SOURCE_PINS.json']
if {kind!r}=='export': names += ['NKO_EXPORT.json','NKO_CLOSURE_PINS.json.sha256']
if {kind!r}=='metadata': names += ['NKO_FULL_GRAPH.json.sha256','NKO_ALL_CRATE_FEATURES.json']
if {kind!r}=='extract': names += ['NKO_EXTRACT_PINS.json','NKO_EXTRACT_OUTPUTS.json.xz','NKO_EXTRACT_OUTPUTS.json.sha256']
if {kind!r}=='preflight': names += ['NKO_PREFLIGHT_PINS.json','NKO_PREFLIGHT_OUTPUTS.json.xz','NKO_PREFLIGHT_OUTPUTS.json.sha256']
if {kind!r}=='kani': names += [str(p.relative_to(b)) for p in b.glob(a+'-graph*')]+[str(p.relative_to(b)) for p in b.glob(a+'-source*')]+[str(p.relative_to(b)) for p in b.glob(a+'-lock*')]
if {kind!r}=='audit':names += [str(p.relative_to(b)) for p in (b/'NKO_audit'/{target!r}).rglob('*') if p.is_file()]+[str(p.relative_to(b)) for modepath in (b/'NKO_audit'/{target!r}).glob('*.json') for row in json.loads(modepath.read_text()).get('results',[]) for p in [b/('NEP_'+modepath.stem+'_'+row['root']+'_REACHABLE.txt')] if p.exists()]+([n for n in ['NKO_LOADED_scan.jsonl','NKO_POOL_LOADED_scan.jsonl'] if (b/n).exists()])
out={{}}
for n in names:
 if n.endswith('.xz'):
  import base64
  out[n+'.base64']=base64.b64encode((b/n).read_bytes()).decode()
 else:out[n]=(b/n).read_text()
if {kind!r}=='export':
 import base64
 out['NKO_CLOSURE_PINS.json.xz.base64']=base64.b64encode((b/'NKO_CLOSURE_PINS.json.xz').read_bytes()).decode()
for name in ['NKO_Driver','NKO_ProofDriver','NKO_PoolProofDriver','NKO_PoolDriver']:
 p=b/'NKO_native'/name
 if p.is_file():out[a+'/'+name+'_BINARY_PIN.json']=json.dumps(dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
print(json.dumps(out))
''');assert r.returncode==0,r.stderr
for n,t in json.loads(r.stdout).items():
 p=E/n;p.parent.mkdir(parents=True,exist_ok=True)
 if n.endswith('.base64'):
  import base64
  (E/n.removesuffix('.base64')).write_bytes(base64.b64decode(t))
 elif n.startswith('NEP_') and n.endswith('_REACHABLE.txt'):
  raw=t.encode();(E/('NKO_'+n+'.sha256')).write_text(hashlib.sha256(raw).hexdigest()+'\n');(E/('NKO_'+n+'.xz')).write_bytes(lzma.compress(raw,preset=6))
 else:p.write_text(t)
assert (E/a/'receipt.json').exists(),'Missing receipt; never resubmit'
rc=json.loads((E/a/'receipt.json').read_text());entry={k:v for k,v in rc.items() if k!='deps_fingerprint'};entry['full_receipt']=a+'/receipt.json'
with (E/'NKO_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(entry)+'\n')
summary={k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps']};summary['axiom_lines']=len(rc['print_axioms']) if isinstance(rc['print_axioms'],list) else rc['print_axioms'];print(json.dumps(summary));sys.exit(rc['exit_status'])
