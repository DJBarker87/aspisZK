"""NFX-owned serial client for unchanged S2W launcher; no shared tool edits."""
from pathlib import Path
import subprocess,json,sys,time,hashlib,shlex,lzma,re,os,atexit
from NLP_read import read_text
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90'
B='/home/dombarker/project-offloads/codex-cx-tx2-common-20261110';C='/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104';W='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025';T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
if (E/'NLP_HOLD').exists():sys.exit(75)
guard=E/'NLP_CLIENT_ACTIVE'; fd=os.open(guard,os.O_CREAT|os.O_EXCL|os.O_WRONLY);os.write(fd,str(os.getpid()).encode());os.close(fd);atexit.register(lambda:guard.unlink(missing_ok=True))
a,kind,target=sys.argv[1:];assert re.fullmatch('NLP_[LKE][0-9]{3}',a) and 1<=int(a[-3:])<=(10 if kind=='kani' else 0 if kind=='extract' else 90) and not (E/a).exists()
if kind=='kani':
 completed=[json.loads(l) for l in (E/'NLP_ATTEMPTS.jsonl').read_text().splitlines()]
 assert sum(r['kind']=='kani' for r in completed)<10,'Kani process budget exhausted'
 # K001 and K018 are retained pre-launch failures, not native invocations.


def ssh(code,data=None,submitted=False):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,code],input=data,capture_output=True,text=True)
  with (E/'NLP_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=retry,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
  if r.returncode!=255:return r
  if submitted:raise RuntimeError('Submitted; recover read-only, never resubmit')
  if retry<10:time.sleep(60)
 raise RuntimeError('Transport exhausted')
disk_checks=[]
for disk_retry in range(7):
 disk=ssh("python3 -c 'import shutil,json;print(json.dumps(dict(free=shutil.disk_usage(\"/home/dombarker/project-offloads\").free)))'")
 assert disk.returncode==0,'disk transport failure'
 disk_row=json.loads(disk.stdout);disk_row['retry']=disk_retry;disk_checks.append(disk_row)
 (E/(a+'-disk.json')).write_text(json.dumps(dict(checks=disk_checks)))
 if disk_row['free']>=40_000_000_000:break
 if disk_retry==6:raise RuntimeError('STOP disk below40GB after six10-minute waits')
 print('disk wait10 minutes',flush=True)
 for minute in range(10):time.sleep(60)
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
 files['NLP_prune.py']=(E/'NLP_prune.py').read_text();sources=list(files);command=['python3','NLP_prune.py']
elif kind=='finalcheck':
 for n in ['NLP_final_checks.py','NLP_cleanup.py','NLP_MODULES.json','NLP_SOURCE_PINS.json','NLP_PATHS.json']:files[n]=(E/n).read_text()
 sources=list(files);command=['python3','NLP_final_checks.py']
elif kind=='cleanup':
 files['NLP_cleanup.py']=(E/'NLP_cleanup.py').read_text();sources=list(files);command=['python3','NLP_cleanup.py']
elif kind=='projection':
 for n in ['NLP_projection_check.py','NLP_TREE_CUT.json','NLP_PREFIX_NATIVE_CUT.json','NLP_CTOR_CUT.json']:files[n]=(E/n).read_text()
 sources=list(files);command=['python3','NLP_projection_check.py']
elif kind=='retention':
 files['NLP_retention.py']=(E/'NLP_retention.py').read_text();sources=list(files);command=['python3','NLP_retention.py']
elif kind=='sourcecheck':
 for n in ['NLP_verify_sources.py','NLP_MODULES.json','NLP_SOURCE_PINS.json']:files[n]=(E/n).read_text()
 sources=list(files);command=['python3','NLP_verify_sources.py']
elif kind=='verify':
 files['NLP_verify_exports.py']=(E/'NLP_verify_exports.py').read_text();sources=list(files);command=['python3','NLP_verify_exports.py']
elif kind=='tools':
 files['NLP_tools.py']=(E/'NLP_tools.py').read_text();sources=list(files);command=['python3','NLP_tools.py']
elif kind=='stage':
 files['NLP_stage.py']=(E/'NLP_stage.py').read_text()
 files['NLP_KMX.patch']=Path('evidence/kani-mitig-20261028/KMX_copy_stubs.patch').read_text()
 sources=list(files);command=['python3','NLP_stage.py']
elif kind=='export':
 files['NLP_export.py']=(E/'NLP_export.py').read_text();files['NLP_MODULES.json']=(E/'NLP_MODULES.json').read_text();sources=list(files);command=['python3','NLP_export.py']
elif kind=='metadata':
 files['NLP_capture_graph.py']=(E/'NLP_capture_graph.py').read_text();files['NLP_EXPECTED_GRAPH_HASHES.json']=(E/'NLP_EXPECTED_GRAPH_HASHES.json').read_text();sources=list(files);command=['python3','NLP_capture_graph.py']
elif kind=='review':
 for n in ['NLP_review.py','NLP_HARNESS.patch','NLP_NATIVE_PAIRS.json','NLP_OCCURRENCES.json','NLP_CLOSED.json','NLP_LEDGER_DELTA.json','NLP_AUDIT_ROOTS.json']:files[n]=(E/n).read_text()
 sources=list(files);command=['python3','NLP_review.py',target]
elif kind in ['extract','preflight']:
 for n in ['NLP_extract.py','NLP_NHR_stage.py','NLP_EXTRACT_OPACITY.json','NLP_EXTRACT_INPUT_PINS.json']:files[n]=(E/n).read_text()
 sources=list(files);command=['python3','NLP_extract.py']+(['--preflight'] if kind=='preflight' else [])
elif kind=='kani':
 files['NLP_gate.py']=(E/'NLP_gate.py').read_text()
 for n,t in json.loads(read_text(E/'NLP_NATIVE_INPUTS.json')).items():files['NLP_src/'+n]=t
 files['NLP_SOURCE_PINS.json']=(E/'NLP_SOURCE_PINS.json').read_text()
 sources=list(files);command=['python3','NLP_gate.py',a+'.json']
elif kind=='lean':
 n='NLP_generated/'+target+'.lean';files[n]=(E/(target+'.lean')).read_text();sources=[n]
 command=[T+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NLP_generated','-o','NLP_objects/'+target+'.olean',n]
 if target in ['NLP_Driver','NLP_ProofDriver','NLP_PoolProofDriver','NLP_PoolDriver']:command+=['-c','NLP_native/'+target+'.c']
elif kind=='link':
 sources=['NLP_native/'+target+'.c','NLP_native/NFA_WALKER.c','NLP_native/NFA_MemoryLimit.c']
 for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:files['NLP_native/'+n]=(E/'NLP_native'/n).read_text()
 command=[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NLP_native/'+target,*sources]
elif kind=='audit':
 sources=['NLP_generated/NLP_ProofDriver.lean','NLP_generated/NLP_Driver.lean','NLP_batch.py','NLP_AUDIT_ROOTS.json','NLP_EXPECTED_IMPORTS.jsonl']+(['NLP_POOL_ROOTS.json'] if target.startswith('pool') else [])
 for n in sources:files[n]=read_text(E/Path(n).name)
 command=['python3','NLP_batch.py',target]
else:raise ValueError(kind)
config=dict(attempt=a,kind=kind,module=target,sources=sources,command=command,env=dict(LEAN_SYSROOT=T,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',TMPDIR=B+'/NLP_tmp',LEAN_PATH=':'.join([B+'/NLP_objects',C+'/NGI_exports_20261105',C+'/NFT_exports_20261104',C+'/NFU_exports_20261104',C+'/NFV_final_objects_20261104',C+'/NGE_exports_20261104',C+'/NGF_exports_20261104',C+'/NFY_exports_20261104',C+'/NFY_priority',W,W+'/objects',C+'/NLP_d_fallback/NFQ_exports_20261104',C+'/NLP_d_fallback',C+'/NLP_pool_fallback/NFR_final_objects_20261104',C+'/NLP_pool_fallback/NFO_final_objects_20261104',C+'/NLP_pool_fallback',C+'/NLP_pool_fallback/NEY_final_objects_20261104',C+'/NLP_pool_fallback/NEX_final_objects_20261104',C+'/NLP_pool_fallback/NEQ_final_objects_20261103',C+'/NLP_pool_fallback/NEM_final_objects_20261102',C+'/NLP_pool_fallback/NEU_final_objects_20261104',C,T+'/lib/lean'])),timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,deps_fingerprint={},expected_time='Focused import elaboration' if kind=='lean' else 'Optimized linker' if kind=='link' else 'Raw ax2 traversal / coherence scan')
if kind in ['extract','preflight']:config['expected_time']='optimized dependency compilation, Charon tx2_common with resume transparent, then Aeneas; unchanged private NHR_stage.py'
config['env']['LEAN_PATH']=':'.join(json.loads((E/'NLP_PATHS.json').read_text()))
if kind=='kani':
 config['native_command']=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+'/NLP_src/crates/aspis-r1-cost-probe/Cargo.toml','--target-dir',B+'/NLP_target','--features','private-leaf-salts,optimized-terminal,program-build','--lib','-j','1','-Z','unstable-options','-Z','function-contracts','-Z','stubbing','--harness-timeout','90s','--exact','--harness',target,'--output-format','regular']
 config['env'].update(CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG='0',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',RUSTFLAGS='-Copt-level=3 -C link-arg=-Wl,--threads=1'+(' --cfg NLP_invert' if os.environ.get('NLP_INVERT') else ''))
 if os.environ.get('NLP_SHORT_CONTROL'):config['env']['RUSTFLAGS']+=' --cfg NLP_short_control'
 if os.environ.get('NLP_BAD_QUERY_WEIGHT_OWNER'):config['env']['RUSTFLAGS']+=' --cfg NLP_bad_query_weight_owner'
 if os.environ.get('NLP_BAD_QUERY_RAW_OWNER'):config['env']['RUSTFLAGS']+=' --cfg NLP_bad_query_raw_owner'
 if os.environ.get('NLP_BAD_POWER'):config['env']['RUSTFLAGS']+=' --cfg NLP_bad_power'
 if os.environ.get('NLP_BAD_NEXT'):config['env']['RUSTFLAGS']+=' --cfg NLP_bad_next'
 if os.environ.get('NLP_BAD_TERMS'):config['env']['RUSTFLAGS']+=' --cfg NLP_bad_terms'
 if os.environ.get('NLP_BAD_RECEIVER_POINTER'):config['env']['RUSTFLAGS']+=' --cfg NLP_bad_receiver_pointer'
 if os.environ.get('NLP_BAD_DESTINATION'):config['env']['RUSTFLAGS']+=' --cfg NLP_bad_destination'
 if os.environ.get('NLP_BAD_RECEIVER'):config['env']['RUSTFLAGS']+=' --cfg NLP_bad_receiver'
 if os.environ.get('NLP_BAD_BACKING'):config['env']['RUSTFLAGS']+=' --cfg NLP_bad_backing'
 if os.environ.get('NLP_BAD_DROP'):config['env']['RUSTFLAGS']+=' --cfg NLP_bad_drop'
 if os.environ.get('NLP_BAD_DECODE_ARG'):config['env']['RUSTFLAGS']+=' --cfg NLP_bad_decode_arg'
 if os.environ.get('NLP_BAD_REPLY'):config['env']['RUSTFLAGS']+=' --cfg NLP_bad_reply'
 if os.environ.get('NLP_BAD_EXPAND'):config['env']['RUSTFLAGS']+=' --cfg NLP_bad_expand'
 if os.environ.get('NLP_BAD_STAGE'):config['env']['RUSTFLAGS']+=' --cfg NLP_bad_stage'
 if os.environ.get('NLP_BAD_VIEW'):config['env']['RUSTFLAGS']+=' --cfg NLP_bad_view'
 if os.environ.get('NLP_BAD_ALLOC'):config['env']['RUSTFLAGS']+=' --cfg NLP_bad_alloc'
 if os.environ.get('NLP_BAD_ERROR'):config['env']['RUSTFLAGS']+=' --cfg NLP_bad_error'
 if os.environ.get('NLP_BAD_BOX_VALUE'):config['env']['RUSTFLAGS']+=' --cfg NLP_bad_box_value'
 if os.environ.get('NLP_CORRUPT_ARGUMENT') is not None:
  z=os.environ['NLP_CORRUPT_ARGUMENT'];assert re.fullmatch('[0-9]',z);config['env']['RUSTFLAGS']+=' --cfg NLP_corrupt'+z
 config['expected_time']='optimized compilation then one native staged cut with local records; no field multiplication'
config['env']['CARGO_TARGET_DIR']=B+'/NLP_target'
files[a+'.json']=json.dumps(config)
r=ssh('python3',f'''from pathlib import Path
import json,hashlib,re,shutil
b=Path({B!r});files=json.loads({json.dumps(files)!r})
for n,t in files.items():
 p=b/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
(b/'NLP_native').mkdir(exist_ok=True);(b/'NLP_objects').mkdir(exist_ok=True);(b/'NLP_tmp').mkdir(exist_ok=True)
x=json.loads((b/{(a+'.json')!r}).read_text());roots=x['env']['LEAN_PATH'].split(':');pins={{}}
modules=[]
if x['kind']=='lean':modules += re.findall(r'^import ([\\w.]+)',(b/x['sources'][0]).read_text(),re.M)
elif x['kind']=='audit':modules += ['NEP_Planted','NEP_Mutations'] if x['module']=='fixtures' else ['NLP_COMBINED_IMPORT']
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
x['deps_fingerprint']={{'selected_objects':pins,'cache_imports_manifest_sha256':hashlib.sha256((b/'NLP_SEED.json').read_bytes()).hexdigest()}}
(b/{(a+'.json')!r}).write_text(json.dumps(x))
''');assert r.returncode==0,r.stderr
r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
r=ssh('python3',f'''from pathlib import Path
import json,hashlib
b=Path({B!r});a={a!r};names=[str(p.relative_to(b)) for p in (b/a).rglob('*') if p.is_file()]+[a+'.json']
if {kind!r}=='prune': names += ['NLP_PRUNE.json']
if {kind!r}=='finalcheck': names += ['NLP_SOURCE_VERIFICATION.json','NLP_TOOL_PINS.json','NLP_EXPORT.json','NLP_CLOSURE_PINS.json.xz','NLP_CLOSURE_PINS.json.sha256','NLP_RETENTION.json','NLP_CLEANUP.json']
if {kind!r}=='cleanup': names += ['NLP_CLEANUP.json']
if {kind!r}=='review': names += ['NLP_REVIEW_'+{target!r}+'.json']
if {kind!r}=='verify': names += ['NLP_EXPORT_VERIFY.json']
if {kind!r}=='projection': names += ['NLP_PROJECTION_CHECK.json']
if {kind!r}=='retention': names += ['NLP_RETENTION.json','NLP_CLEANUP.json']
if {kind!r}=='sourcecheck': names += ['NLP_SOURCE_VERIFICATION.json']
if {kind!r}=='tools': names += ['NLP_TOOL_PINS.json']
if {kind!r}=='stage': names += ['NLP_STAGE.json','NLP_SOURCE_PINS.json']
if {kind!r}=='export': names += ['NLP_EXPORT.json','NLP_CLOSURE_PINS.json.sha256']
if {kind!r}=='metadata': names += ['NLP_FULL_GRAPH.json.sha256','NLP_ALL_CRATE_FEATURES.json']
if {kind!r}=='extract': names += ['NLP_EXTRACT_PINS.json','NLP_EXTRACT_OUTPUTS.json.xz','NLP_EXTRACT_OUTPUTS.json.sha256']
if {kind!r}=='preflight': names += ['NLP_PREFLIGHT_PINS.json','NLP_PREFLIGHT_OUTPUTS.json.xz','NLP_PREFLIGHT_OUTPUTS.json.sha256']
if {kind!r}=='kani': names += [str(p.relative_to(b)) for p in b.glob(a+'-graph*')]+[str(p.relative_to(b)) for p in b.glob(a+'-source*')]+[str(p.relative_to(b)) for p in b.glob(a+'-lock*')]
if {kind!r}=='audit':names += [str(p.relative_to(b)) for p in (b/'NLP_audit'/{target!r}).rglob('*') if p.is_file()]+[str(p.relative_to(b)) for modepath in (b/'NLP_audit'/{target!r}).glob('*.json') for row in json.loads(modepath.read_text()).get('results',[]) for p in [b/('NEP_'+modepath.stem+'_'+row['root']+'_REACHABLE.txt')] if p.exists()]+([n for n in ['NLP_LOADED_scan.jsonl','NLP_POOL_LOADED_scan.jsonl'] if (b/n).exists()])
out={{}}
for n in names:
 if n.endswith('.xz'):
  import base64
  out[n+'.base64']=base64.b64encode((b/n).read_bytes()).decode()
 else:out[n]=(b/n).read_text()
if {kind!r}=='export':
 import base64
 out['NLP_CLOSURE_PINS.json.xz.base64']=base64.b64encode((b/'NLP_CLOSURE_PINS.json.xz').read_bytes()).decode()
for name in ['NLP_Driver','NLP_ProofDriver','NLP_PoolProofDriver','NLP_PoolDriver']:
 p=b/'NLP_native'/name
 if p.is_file():out[a+'/'+name+'_BINARY_PIN.json']=json.dumps(dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
print(json.dumps(out))
''');assert r.returncode==0,r.stderr
for n,t in json.loads(r.stdout).items():
 p=E/n;p.parent.mkdir(parents=True,exist_ok=True)
 if n.endswith('.base64'):
  import base64
  (E/n.removesuffix('.base64')).write_bytes(base64.b64decode(t))
 elif n.startswith('NEP_') and n.endswith('_REACHABLE.txt'):
  raw=t.encode();(E/('NLP_'+n+'.sha256')).write_text(hashlib.sha256(raw).hexdigest()+'\n');(E/('NLP_'+n+'.xz')).write_bytes(lzma.compress(raw,preset=6))
 else:p.write_text(t)
assert (E/a/'receipt.json').exists(),'Missing receipt; never resubmit'
rc=json.loads((E/a/'receipt.json').read_text());entry={k:v for k,v in rc.items() if k!='deps_fingerprint'};entry['full_receipt']=a+'/receipt.json'
with (E/'NLP_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(entry)+'\n')
summary={k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps']};summary['axiom_lines']=len(rc['print_axioms']) if isinstance(rc['print_axioms'],list) else rc['print_axioms'];print(json.dumps(summary));sys.exit(rc['exit_status'])
