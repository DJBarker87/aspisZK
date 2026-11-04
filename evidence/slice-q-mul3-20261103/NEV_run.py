"""Own serial validation runner; unchanged S2W scope runner supplies receipts."""
from pathlib import Path
import subprocess, json, sys, time, shlex, hashlib, os, difflib
E=Path(__file__).resolve().parent
# Serial launch discipline is enforced by the worker: await each receipt before
# another invocation. Do not wrap the host launcher in an additional flock.
B='/home/dombarker/project-offloads/codex-cx-slice-q-mul3-20261029'
H='dombarker@100.108.41.90'
C='/home/dombarker/project-offloads/codex-cx-slice-q-mul3-cache-20261029'
W='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025'
a,kind,target=sys.argv[1:]
assert a.startswith('NEV_') and int(a[-3:]) <= (20 if kind=='extract' else 70 if kind=='kani' else 120)
assert not (E/(a+'-launcher.log')).exists()
def ssh(code, data=None, submitted=False):
    for retry in range(11):
        r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,code],input=data,capture_output=True,text=True)
        with (E/'NEV_TRANSPORT.jsonl').open('a') as f: f.write(json.dumps(dict(attempt=a,retry=retry,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
        if r.returncode!=255: return r
        if submitted: raise RuntimeError('Submitted transport lost: recover read-only, never resubmit')
        if retry<10: time.sleep(60)
    raise RuntimeError('Transport exhausted')
for retry in range(11):
    code=f'''from pathlib import Path
import subprocess,json,sys
b=Path({B!r})
with (b/{(a+'-barrier-'+str(retry)+'.log')!r}).open('w') as f:
 r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/{(a+'-reservation.json')!r})],stdout=f,stderr=subprocess.STDOUT)
p=b/{(a+'-reservation.json')!r}
print(p.read_text() if p.exists() else 'MISSING')
sys.exit(r.returncode)
'''
    r=ssh('python3',code)
    (E/(a+f'-barrier-{retry}.log')).write_text(r.stdout+r.stderr)
    try: ad=json.loads(r.stdout)
    except json.JSONDecodeError:
        if retry==0: time.sleep(30); continue
        raise RuntimeError('STOP host admission JSON missing')
    (E/(a+'-admission.json')).write_text(json.dumps(dict(exit=r.returncode,reservation=ad)))
    if r.returncode==0 and ad.get('allowed') is True: break
    if (r.returncode==78 or ad.get('allowed') is False) and retry<10:
        print('reservation wait',flush=True);time.sleep(180);continue
    raise RuntimeError('STOP host admission')
files={}
sources=[]
env=dict(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='1',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG='0',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',RUSTFLAGS='-C link-arg=-Wl,--threads=1',TMPDIR=B+'/NEV_tmp',LEAN_PATH=B+'/NEV_objects:'+C+'/NEI_exports_20261103:'+C+'/NEG_results_20261101:'+C+'/NEG_exports_20261029:'+C+'/NEB_exports_20261029:'+C+':/home/dombarker/project-offloads/codex-cx-reconcile-cache-20261028/objects:'+W+':'+W+'/objects')
if os.environ.get('NEV_SINT2_FIRST')=='1':
    env['LEAN_PATH']=':'.join([B+'/NEV_objects',W,W+'/objects']+[v for v in env['LEAN_PATH'].split(':') if v not in [B+'/NEV_objects',W,W+'/objects']])
if os.environ.get('NEV_ARCHIVE_IMPORT')=='1':
    archive_set=os.environ.get('NEV_ARCHIVE_SET','NEV_exports_20261102')
    assert archive_set.startswith('NEV_exports_') and archive_set.replace('_','').isalnum()
    env['LEAN_PATH']=env['LEAN_PATH'].replace(B+'/NEV_objects',C+'/'+archive_set,1)
deps={}
native=[]
if kind=='lean':
    n='NEV_generated/'+target+'.lean'; files[n]=(json.loads((E/'NEV_PREREQUISITES.json').read_text())['sources'][target]['text'] if os.environ.get('NEV_UNCHANGED_MODULE')=='1' else (E/(target+'.lean')).read_text());sources=[n]
    command=['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NEV_generated','-o','NEV_objects/'+target+'.olean',n]
    library=json.loads((E/'NEV_SOURCE.json').read_text())['library']
    if os.environ.get('NEV_HEADLINE')=='1':library.update({p['object_path']:p['object_sha256'] for p in json.loads((E/'NEV_HEADLINE_OBJECT_PINS.json').read_text())['entries'] if p['module']=='Aeneas' or p['module'].startswith('Aeneas.')})
    deps['selected_objects']={p:dict(path=p,sha256=h) for p,h in library.items()}
elif kind=='kani':
    payload_path=(E/os.environ.get('NEV_KANI_PAYLOAD','NEV_PAYLOAD.json')).resolve()
    assert payload_path.parent==E and payload_path.name.startswith('NEV_')
    payload=json.loads(payload_path.read_text())
    files={ 'NEV_src/'+n:t for n,t in payload.items() }
    files['NEV_FROZEN.json']=(E/'NEV_FROZEN.json').read_text()
    for n in ['gate','graph']: files['NEV_'+n+'.py']=(E/('NEV_'+n+'.py')).read_text()
    sources=list(files)+['NEV_src/Cargo.lock','NEV_SOURCE_PINS.json']
    (E/a).mkdir(exist_ok=True)
    frozen_payload=json.loads((E/'NEV_FROZEN.json').read_text())
    archived_patch=''.join(''.join(difflib.unified_diff(frozen_payload.get(name,'').splitlines(True),text.splitlines(True),fromfile='a/'+name,tofile='b/'+name)) for name,text in payload.items())
    (E/a/'NEV_harness.patch').write_text(archived_patch)
    native=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+'/NEV_src/crates/aspis-r1-cost-probe/Cargo.toml','--target-dir',B+'/NEV_target','--lib','--features','private-leaf-salts,optimized-terminal,program-build','-j','1','-Z','unstable-options','-Z','function-contracts','-Z','stubbing','--harness-timeout','90s','--exact','--harness',target,'--output-format','terse']
    if os.environ.get('NEV_ROOT')=='core':
        native[native.index('--manifest-path')+1]=B+'/NEV_src/crates/aspis-core/Cargo.toml'
        native[native.index('--features')+1]='r0'
    if os.environ.get('NEV_RUST_CFG'):env['RUSTFLAGS']+=' --cfg '+os.environ['NEV_RUST_CFG']
    if os.environ.get('NEV_CODEGEN_ONLY')=='1':native+=['--only-codegen']
    command=['python3','NEV_gate.py',a+'.json']
elif kind=='native':
    if os.environ.get('NEV_NATIVE_OVERFLOW_CHECKS')=='false':env['CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS']='false'
    family=os.environ.get('NEV_NATIVE_FAMILY','line');assert family in ['line','circle','prefix','push','row','accumulate','dots','field']
    for name in [f'NEV_{family}_native.py',f'NEV_{family}_native.rs','NEV_FROZEN.json']:
        files[name]=(json.loads((E/'NEV_FIELD_NATIVE_INPUT.json').read_text())['rust_source'] if family=='field' and name=='NEV_field_native.rs' else (E/name).read_text())
    if family=='field':files['NEV_FIELD_TEST_INPUTS.json']=(E/'NEV_FIELD_TEST_INPUTS.json').read_text()
    if os.environ.get('NEV_WRONG'):env['NEV_WRONG']=os.environ['NEV_WRONG']
    sources=list(files);command=['python3',f'NEV_{family}_native.py']
elif kind=='inspect':
    files['NEV_goto_inspect.py']=(E/'NEV_goto_inspect.py').read_text()
    sources=list(files);command=['python3','NEV_goto_inspect.py']
else:
    files['NEV_extract.py']=(E/'NEV_extract.py').read_text()
    files['NEV_FROZEN.json']=(E/'NEV_FROZEN.json').read_text()
    reference_path=E/os.environ.get('NEV_REFERENCE','NEV_reference.rs.txt')
    if not reference_path.exists():
        from NEV_restore import references
        references()
    files['NEV_reference.rs']=reference_path.read_text()
    if (E/'NEV_row_reference.rs').exists():files['NEV_row_reference.rs']=(E/'NEV_row_reference.rs').read_text()
    if os.environ.get('NEV_EXTRACT_CONFIG'):env['NEV_EXTRACT_CONFIG']=os.environ['NEV_EXTRACT_CONFIG']
    sources=list(files);command=['python3','NEV_extract.py']
cfg=dict(attempt=a,kind=kind,module=target,sources=sources,command=command,native_command=native,env=env,timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,deps_fingerprint=deps,expected_time='Focused elaboration' if kind=='lean' else 'Optimized reference compilation and Charon/Aeneas IR generation; no arithmetic execution' if kind=='extract' else 'Optimized frozen-body fidelity fixtures with matched controls; no universal arithmetic gate' if kind=='native' else 'Optimized compile then named native check; multiplication excluded',copy_patch_sha256='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67')
files[a+'.json']=json.dumps(cfg)
code=f'''from pathlib import Path
import json,hashlib
b=Path({B!r});files=json.loads({json.dumps(files)!r})
# Restore the private scaffold to frozen bytes before applying cfg-only payload.
if {kind!r}=='kani':
 frozen=json.loads(files['NEV_FROZEN.json'])
 for n,t in frozen.items():
  q=b/'NEV_src'/n
  if q.is_file():
   assert not q.is_symlink(),str(q)
   if n=='Cargo.lock':assert q.read_text()==t,'STOP existing lock drift'
   else:q.write_text(t)
for n,t in files.items():
 p=b/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
pins=json.loads((b/'NEV_SOURCE_PINS.json').read_text()) if (b/'NEV_SOURCE_PINS.json').exists() else {{}}
for n in files:
 if n.startswith('NEV_src/'):pins[n[8:]]=hashlib.sha256((b/n).read_bytes()).hexdigest()
(b/'NEV_SOURCE_PINS.json').write_text(json.dumps(pins))
x=json.loads((b/{(a+'.json')!r}).read_text())
if x['kind']=='lean':(b/'NEV_objects'/{target!r}).parent.mkdir(parents=True,exist_ok=True)
if x['kind']=='lean':
 roots=x['env']['LEAN_PATH'].split(':')
 # Pin every selected Aeneas/AeneasMeta library object and sidecar, not merely
 # the later fallback that supplied the predecessor's original library map.
 for old in list(x['deps_fingerprint']['selected_objects']):
  rel=old.split('/objects/')[-1]
  if not rel.startswith(('Aeneas.','Aeneas/','AeneasMeta.','AeneasMeta/')):continue
  q=next((Path(root)/rel for root in roots if (Path(root)/rel).is_file()),None)
  assert q is not None,rel
  for z in [q,Path(str(q)+'.private'),Path(str(q)+'.server'),q.with_suffix('.ir')]:
   if z.is_file():x['deps_fingerprint']['selected_objects'][str(z)]=dict(path=str(z),sha256=hashlib.sha256(z.read_bytes()).hexdigest())
 for line in (b/x['sources'][0]).read_text().splitlines():
  if not line.startswith('import '):continue
  for module in line[7:].split():
   key=module.replace('.','/')+'.olean'
   p=next((Path(root)/key for root in roots if (Path(root)/key).is_file()),None)
   if p is None:raise FileNotFoundError(module)
   for q in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
    if q.exists():x['deps_fingerprint']['selected_objects'][str(q)]=dict(path=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest())
 (b/{(a+'.json')!r}).write_text(json.dumps(x))
'''
r=ssh('python3',code);assert r.returncode==0,r.stderr
(E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
launcher='S2W_run_host.py'
r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 '+launcher+' '+a+'.json',submitted=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
code=f'''from pathlib import Path
import json
b=Path({B!r});a={a!r}
names=[str(p.relative_to(b)) for p in (b/a/'sources').rglob('*') if p.is_file()]+[a+'/receipt.json',a+'/stdout.log',a+'/time.log',a+'-graph-check.json',a+'-source-check.json',a+'-graph.stderr',a+'-lock-check.json',a+'-rule16-check.json',a+'-frozen-source-check.json',a+'-tool-check.json','NEV_EXTRACTION_PINS.json','NEV_NATIVE_METADATA.json','NEV_NATIVE_PINS.json',a+'.json']

if {kind!r}=='extract':
 names += [str(p.relative_to(b)) for p in (b/'NEV_extracted').rglob('*.lean')]
result={{n:(b/n).read_text() for n in names if (b/n).is_file()}}
if {kind!r}=='extract' and (b/'NEV_isolated/src/lib.rs').is_file():
 for n in ['src/lib.rs','src/NEV_pairing.rs','Cargo.toml','Cargo.lock']:
  if (b/'NEV_isolated'/n).is_file():result[a+'/NEV_isolation_'+n.replace('/','_')+'.txt']=(b/'NEV_isolated'/n).read_text()
print(json.dumps(result))
'''
r=ssh('python3',code);assert r.returncode==0,r.stderr
out=json.loads(r.stdout)
for n,t in out.items():
    p=E/(n+'.txt' if n.endswith('_Template.lean') else n);p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
assert a+'/receipt.json' in out,'No receipt: stop, do not resubmit'
if kind=='native':
    for name in ['NEV_NATIVE_PINS.json','NEV_NATIVE_METADATA.json']:
        if name in out:(E/a/name).write_text(out[name])
if kind=='extract' and 'NEV_EXTRACTION_PINS.json' in out:(E/a/'NEV_EXTRACTION_PINS.json').write_text(out['NEV_EXTRACTION_PINS.json'])
rc=json.loads(out[a+'/receipt.json'])
with (E/'NEV_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(rc)+'\n')
print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}),flush=True)
print(out[a+'/stdout.log'][-(1000 if kind=='kani' else 3500):],flush=True)

sys.exit(rc["exit_status"])
