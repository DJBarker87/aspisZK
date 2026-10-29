"""Own serial validation runner; unchanged S2W scope runner supplies receipts."""
from pathlib import Path
import subprocess, json, sys, time, shlex, hashlib, os
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-cx-slice-q-leaves-20261029'
H='dombarker@100.108.41.90'
C='/home/dombarker/project-offloads/codex-cx-slice-q-leaves-cache-20261029'
W='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025'
a,kind,target=sys.argv[1:]
assert a.startswith('NEA_') and int(a[-3:]) <= (20 if kind=='extract' else 80)
assert not (E/(a+'-launcher.log')).exists()
def ssh(code, data=None, submitted=False):
    for retry in range(11):
        r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,code],input=data,capture_output=True,text=True)
        with (E/'NEA_TRANSPORT.jsonl').open('a') as f: f.write(json.dumps(dict(attempt=a,retry=retry,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
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
env=dict(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='1',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG='0',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',RUSTFLAGS='-C link-arg=-Wl,--threads=1',TMPDIR=B+'/NEA_tmp',LEAN_PATH=B+'/NEA_objects:'+C+':'+W+':'+W+'/objects')
deps={}
native=[]
if kind=='lean':
    n='NEA_generated/'+target+'.lean'; files[n]=(E/(target+'.lean')).read_text();sources=[n]
    command=['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NEA_generated','-o','NEA_objects/'+target+'.olean',n]
    library=json.loads((E/'NEA_SOURCE.json').read_text())['library']
    deps['selected_objects']={p:dict(path=p,sha256=h) for p,h in library.items()}
elif kind=='kani':
    payload=json.loads((E/'NEA_PAYLOAD.json').read_text())
    files={ 'NEA_src/'+n:t for n,t in payload.items() }
    for n in ['gate','graph']: files['NEA_'+n+'.py']=(E/('NEA_'+n+'.py')).read_text()
    sources=list(files)+['NEA_src/Cargo.lock','NEA_SOURCE_PINS.json']
    (E/a).mkdir(exist_ok=True)
    (E/a/'NEA_harness.patch').write_text((E/'NEA_native.patch').read_text())
    native=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+'/NEA_src/crates/aspis-r1-cost-probe/Cargo.toml','--target-dir',B+'/NEA_target','--lib','--features','private-leaf-salts,optimized-terminal,program-build','-j','1','-Z','unstable-options','-Z','function-contracts','-Z','stubbing','--harness-timeout','90s','--exact','--harness',target,'--output-format','terse']
    if os.environ.get('NEA_ROOT')=='core':
        native[native.index('--manifest-path')+1]=B+'/NEA_src/crates/aspis-core/Cargo.toml'
        native[native.index('--features')+1]='r0'
    if os.environ.get('NEA_RUST_CFG'):env['RUSTFLAGS']+=' --cfg '+os.environ['NEA_RUST_CFG']
    command=['python3','NEA_gate.py',a+'.json']
elif kind=='inspect':
    files['NEA_goto_inspect.py']=(E/'NEA_goto_inspect.py').read_text()
    sources=list(files);command=['python3','NEA_goto_inspect.py']
else:
    files['NEA_extract.py']=(E/'NEA_extract.py').read_text()
    files['NEA_reference.rs']=(E/os.environ.get('NEA_REFERENCE','NEA_reference.rs.txt')).read_text()
    if os.environ.get('NEA_EXTRACT_CONFIG'):env['NEA_EXTRACT_CONFIG']=os.environ['NEA_EXTRACT_CONFIG']
    sources=list(files);command=['python3','NEA_extract.py']
cfg=dict(attempt=a,kind=kind,module=target,sources=sources,command=command,native_command=native,env=env,timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,deps_fingerprint=deps,expected_time='Focused elaboration' if kind=='lean' else 'Optimized compile then named native check; multiplication excluded',copy_patch_sha256='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67')
files[a+'.json']=json.dumps(cfg)
code=f'''from pathlib import Path
import json,hashlib
b=Path({B!r});files=json.loads({json.dumps(files)!r})
for n,t in files.items():
 p=b/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
pins=json.loads((b/'NEA_SOURCE_PINS.json').read_text())
for n in files:
 if n.startswith('NEA_src/'):pins[n[8:]]=hashlib.sha256((b/n).read_bytes()).hexdigest()
(b/'NEA_SOURCE_PINS.json').write_text(json.dumps(pins))
x=json.loads((b/{(a+'.json')!r}).read_text())
if x['kind']=='lean':(b/'NEA_objects'/{target!r}).parent.mkdir(parents=True,exist_ok=True)
if x['kind']=='lean':
 roots=x['env']['LEAN_PATH'].split(':')
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
names=[a+'/receipt.json',a+'/stdout.log',a+'/time.log',a+'-graph-check.json',a+'-source-check.json',a+'-graph.stderr',a+'-lock-check.json','NEA_EXTRACTION_PINS.json',a+'.json']
print(json.dumps({{n:(b/n).read_text() for n in names if (b/n).is_file()}}))
'''
r=ssh('python3',code);assert r.returncode==0,r.stderr
out=json.loads(r.stdout)
for n,t in out.items():
    p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
assert a+'/receipt.json' in out,'No receipt: stop, do not resubmit'
if kind=='extract' and 'NEA_EXTRACTION_PINS.json' in out:(E/a/'NEA_EXTRACTION_PINS.json').write_text(out['NEA_EXTRACTION_PINS.json'])
rc=json.loads(out[a+'/receipt.json'])
with (E/'NEA_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(rc)+'\n')
print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}),flush=True)
print(out[a+'/stdout.log'][-(1000 if kind=='kani' else 3500):],flush=True)
