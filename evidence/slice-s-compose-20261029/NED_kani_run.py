"""Serial scratch-only Kani/metadata driver using the unchanged host launcher."""
from pathlib import Path
import subprocess,json,sys,time,hashlib,shlex,tomllib
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-slice-s-compose-20261029';H='dombarker@100.108.41.90'
a,kind,harness=sys.argv[1:];assert kind in ['metadata','kani'];assert a.startswith('NED_M' if kind=='metadata' else 'NED_K')
assert not (E/a).exists();assert len(list(E.glob('NED_K*/receipt.json')))<40
active=E/'NED_ACTIVE.json';assert not active.exists();active.write_text(json.dumps(dict(attempt=a,kind=kind)))
def ssh(code,stdin=None,submitted=False):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2',H,code],input=stdin,text=True,capture_output=True)
  with (E/'NED_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=retry,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
  if r.returncode!=255 or submitted:return r
  if retry<10:time.sleep(60)
 raise SystemExit('STOP transport exhausted')
for retry in range(11):
 code=f'''from pathlib import Path
import subprocess,json,sys
b=Path({B!r});p=b/{(a+'-barrier-'+str(retry)+'.log')!r}
with p.open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/{(a+'-reservation.json')!r})],stdout=f,stderr=subprocess.STDOUT)
print(p.read_text());sys.exit(r.returncode)
'''
 r=ssh('python3',code);(E/(a+f'-barrier-{retry}.log')).write_text(r.stdout+r.stderr)
 try:ad=next(json.loads(l) for l in r.stdout.splitlines() if l.startswith('{'))
 except (StopIteration,json.JSONDecodeError):
  if retry==0:time.sleep(30);continue
  raise SystemExit('STOP reservation JSON missing')
 (E/(a+'-admission.json')).write_text(json.dumps(dict(exit=r.returncode,reservation=ad)))
 if r.returncode==0 and ad.get('allowed') is True:break
 if (r.returncode==78 or ad.get('allowed') is False) and retry<10:time.sleep(180);continue
 raise SystemExit('STOP admission')
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
probe=tomllib.loads(subprocess.check_output(['git','show',rev+':crates/aspis-r1-cost-probe/Cargo.toml'],text=True));stmt=tomllib.loads(subprocess.check_output(['git','show',rev+':crates/aspis-statement/Cargo.toml'],text=True))
features=['r0','pool-v1-kernel']+[s.split('/',1)[1] for s in probe['features']['optimized-terminal']]
closure=set()
def visit(n):
 if n in closure:return
 closure.add(n)
 for v in stmt['features'].get(n,[]):
  if '/' not in v and not v.startswith('dep:'):visit(v)
for n in features:visit(n)
native=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+'/NED_src/crates/aspis-statement/Cargo.toml','--target-dir',B+'/NED_target','--lib','--features',','.join(features),'-j','1','-Z','unstable-options','-Z','function-contracts','-Z','stubbing','--harness-timeout','90s','--exact','--harness',harness,'--output-format','terse']
if kind=='metadata':native=[]
env=dict(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG='0',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',RUSTFLAGS='-C link-arg=-Wl,--threads=1',TMPDIR=B+'/NED_tmp')
files={'NED_kani_gate.py':(E/'NED_kani_gate.py').read_text(),'NED_contract_controls.patch':(E/'NED_contract_controls.patch').read_text(),'NED_KMX_copy_stubs.patch':(E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch').read_text(),'NED_RUST_SOURCE_PINS.json':(E/'NED_RUST_SOURCE_PINS.json').read_text(),'NED_FROZEN_GRAPH.json':subprocess.check_output(['git','show','HEAD:evidence/leaf-p6-11-20261027/LPm_frozen_graph.json'],text=True)}
cfg=dict(attempt=a,kind=kind,module=harness,command=['python3','NED_kani_gate.py',a+'.json'],native_command=native,sources=list(files)+['NED_RUST_SHA256.json','NED_src/Cargo.lock','NED_src/crates/aspis-statement/src/lib.rs','NED_src/crates/aspis-statement/src/NED_controls.rs'],env=env,timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,deps_fingerprint=dict(frozen_revision=rev,frozen_source_pinset='NED_RUST_SOURCE_PINS.json'),statement_features=','.join(features),required_statement_features=sorted(closure),expected_time='frozen dependency/feature validation, optimized compilation, then one named ABI contract fidelity control; no native field arithmetic or protocol loop',copy_patch_sha256='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67')
files[a+'.json']=json.dumps(cfg,indent=1)
code=f'''from pathlib import Path
import json,subprocess,hashlib
b=Path({B!r});s=b/'NED_src';files=json.loads({json.dumps(files)!r})
for n,v in files.items():(b/n).write_text(v)
(b/'NED_tmp').mkdir(exist_ok=True)
if not (b/'NED_RUST_SHA256.json').exists():
 pins=json.loads((b/'NED_RUST_SOURCE_PINS.json').read_text());errors=[]
 for n,p in pins['files'].items():
  data=(s/n).read_bytes();h=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\\0'+data).hexdigest()
  if h!=p['git_blob']:errors.append(n)
 assert not errors,('frozen upload mismatch',errors)
 for patch in ['NED_KMX_copy_stubs.patch','NED_contract_controls.patch']:
  subprocess.run(['git','apply',str(b/patch)],cwd=s,check=True,capture_output=True)
 out={{str(p.relative_to(s)):hashlib.sha256(p.read_bytes()).hexdigest() for p in s.rglob('*') if p.is_file()}}
 (b/'NED_RUST_SHA256.json').write_text(json.dumps(out,indent=1)+'\\n')
 # The only frozen-source edit is the crate-level cfg(kani) hook/attribute.
 lib=(s/'crates/aspis-statement/src/lib.rs').read_text()
 erase=lib.replace('#![cfg_attr(kani, feature(allocator_api))]\\n','').replace('\\n#[cfg(kani)]\\n#[path="../../../KMX_stubs.rs"]\\nmod KMX_stubs;\\n#[cfg(kani)]\\nmod NED_controls;\\n','')
 original=pins['files']['crates/aspis-statement/src/lib.rs']['git_blob'];data=erase.encode()
 assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\\0'+data).hexdigest()==original,'cfg-only erasure failed'
print((b/'NED_RUST_SHA256.json').read_text())
'''
r=ssh('python3',code);(E/(a+'-upload.log')).write_text(r.stderr);assert r.returncode==0,r.stderr
(E/'NED_RUST_SHA256.json').write_text(r.stdout)
(E/(a+'.json')).write_text(json.dumps(cfg,indent=1)+'\n')
r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
code=f'''from pathlib import Path
import json
b=Path({B!r});names={[a+'/receipt.json',a+'/stdout.log',a+'/time.log',a+'-source-check.json',a+'-tools.json',a+'-metadata-pin.json',a+'-metadata.stderr',a+'-graph-check.json',a+'-lock-check.json']!r}
print(json.dumps({{n:(b/n).read_text() for n in names if (b/n).exists()}}))
'''
r=ssh('python3',code);assert r.returncode==0,r.stderr;out=json.loads(r.stdout)
for n,v in out.items():p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(v)
assert a+'/receipt.json' in out,'submitted attempt unresolved; never resubmit'
rc=json.loads(out[a+'/receipt.json'])
with (E/'NED_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(rc)+'\n')
active.unlink();print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps']}));print(out[a+'/stdout.log'][-2500:])
sys.exit(rc['exit_status'])
