"""Lane-owned serial wrapper around unchanged S2W launchers."""
from pathlib import Path
import subprocess,json,sys,time,shlex,hashlib,os
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-native-front4b-20261028';H='dombarker@100.108.41.90'
a,kind,target=sys.argv[1:];limit=80 if kind=='kani' else (20 if kind=='extract' else 80)
assert int(a[-3:])<=limit
assert not (E/a).exists()
# A control of a timed-out property has the same solver shape. Never launch it.
if kind=='kani' and os.environ.get('NDM_INVERT'):
 previous=f"NDM_K{int(a[-3:])-1:03d}"
 log=E/previous/'stdout.log'
 if log.exists():
  content=log.read_text().lower()
  assert not any(x in content for x in ['timed out','timeout after','time out','killed by signal','out of memory']), 'split timed-out shape before control'

while kind=='kani' and (E/'NDM_PAUSE_KANI').exists():time.sleep(1)
active=E/'NDM_ACTIVE.json';assert not active.exists(),active
active.write_text(json.dumps(dict(attempt=a)))
def ssh(code,stdin=None,submitted=False):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2',H,code],input=stdin,capture_output=True,text=True)
  with (E/'NDM_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=retry,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
  if r.returncode!=255 or submitted:return r
  if retry<10:time.sleep(60)
 raise SystemExit('transport exhausted')
for retry in range(11):
 code=f'''import subprocess,json,pathlib,sys
b=pathlib.Path({B!r});p=b/{(a+'-barrier-'+str(retry)+'.log')!r}
with p.open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/{(a+'-reservation.json')!r})],stdout=f,stderr=subprocess.STDOUT)
print(p.read_text());sys.exit(r.returncode)
'''
 r=ssh('python3',code);(E/(a+f'-barrier-{retry}.log')).write_text(r.stdout+r.stderr)
 try:ad=next(json.loads(l) for l in r.stdout.splitlines() if l.startswith('{'))
 except (StopIteration,json.JSONDecodeError):
  if retry==0:time.sleep(30);continue
  raise SystemExit('STOP infrastructure: admission JSON missing')
 (E/(a+'-admission.json')).write_text(json.dumps(dict(exit=r.returncode,reservation=ad)))
 if r.returncode==0 and ad.get('allowed') is True:break
 if (r.returncode==78 or ad.get('allowed') is False) and retry<10:print('reservation wait',flush=True);time.sleep(180);continue
 raise SystemExit('STOP infrastructure admission')
files={'NDM_gate.py':(E/'NDM_gate.py').read_text(),'NDM_graph.py':(E/'NDM_graph.py').read_text()}
if kind=='kani':
 from NDM_patch import files as patch_files
 for n,s in patch_files().items():files['NDM_src/'+n]=s
 (E/a).mkdir(exist_ok=True)
 (E/a/'NDM_harness.patch').write_text((E/'NDM_native.patch').read_text())
 sources=['NDM_gate.py','NDM_graph.py','NDM_SOURCE_PINS.json']+list(n for n in files if n.endswith('.rs'))+['NDM_src/Cargo.lock','NDM_src/Cargo.toml']
 native=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+'/NDM_src/programs/r1-cost-probe/Cargo.toml','--target-dir',B+'/NDM_target','--lib','--features','pool-adapter,private-leaf-salts','-j','1','-Z','unstable-options','-Z','function-contracts','-Z','stubbing','--harness-timeout','90s','--exact','--harness',target,'--output-format','terse']
 command=['python3','NDM_gate.py',a+'.json']
elif kind=='extract':
 files['NDM_extract.py']=(E/'NDM_extract.py').read_text();files['NDM_src/programs/r1-cost-probe/src/NDM_reference.rs']=(E/'NDM_reference.rs.txt').read_text();sources=['NDM_extract.py','NDM_src/programs/r1-cost-probe/src/NDM_reference.rs'];native=[];command=['python3','NDM_extract.py']
else:
 files['NDM_generated/'+target+'.lean']=(E/(target+'.lean')).read_text();sources=['NDM_generated/'+target+'.lean']
 native=[];command=['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NDM_generated','-o','NDM_objects/'+target+'.olean',sources[0]]
env=dict(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG='0',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',RUSTFLAGS='-C link-arg=-Wl,--threads=1',TMPDIR=B+'/NDM_tmp',LEAN_PATH=B+'/NDM_objects:/home/dombarker/project-offloads/codex-cx-native-front4-20261028/NDG_objects:/home/dombarker/project-offloads/codex-cx-front4-cache-20261028:/home/dombarker/project-offloads/codex-cx-sound-int2-20261025:/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects')
if os.environ.get('NDM_EXTRA'):env['NDM_EXTRA']=os.environ['NDM_EXTRA']
if os.environ.get('NDM_EXTRACT_PARSER'):env['NDM_EXTRACT_PARSER']=os.environ['NDM_EXTRACT_PARSER']
if os.environ.get('NDM_RUST_CFG'):env['RUSTFLAGS']+=' --cfg '+os.environ['NDM_RUST_CFG']
cfg=dict(attempt=a,kind=kind,module=target,sources=sources,command=command,native_command=native,env=env,timeout=240,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,deps_fingerprint={'source_pinset':'NDM_SOURCE.json','library_pinset':'NDM_SOURCE.json:library'},expected_time='optimized compile then one contract/shape proof; no field multiplication',copy_patch_sha256='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67')
if kind=='lean':
 cfg['deps_fingerprint']['selected_objects']={p:dict(path=p,sha256=h) for p,h in json.loads((E/'NDM_SOURCE.json').read_text())['library'].items()}
 cfg['deps_fingerprint']['coherent_object_manifest_sha256']=__import__('hashlib').sha256((E/'NDM_COHERENT_OBJECT_PINS.json').read_bytes()).hexdigest()
 pins=json.loads((E/'NDM_COHERENT_OBJECT_PINS.json').read_text())
 for n in ['AdapterRwModel','AdapterRwTypes','AdapterRwScalar','AdapterRwSdkSnapshots','AdapterRwRuntimeAdmission','S2TrustedSdkBorrow']:
  for root in ['/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/','/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/']:
   p=root+n+'.olean'
   if p in pins:cfg['deps_fingerprint']['selected_objects'][p]=pins[p];break
 if target=='NDM_Audit':
  cfg['deps_fingerprint']['selected_objects']=json.loads((E/'NDM_AUDIT_PINS.json').read_text())['selected_objects']
  files['NDM_AUDIT_PINS.json']=(E/'NDM_AUDIT_PINS.json').read_text()
  sources.append('NDM_AUDIT_PINS.json')
files[a+'.json']=json.dumps(cfg,indent=2)
# Upload after admission; snapshots permit exact local reconstruction.
for n,s in files.items():
 if n.startswith('NDM_src/'):continue
 p=E/a/'sources'/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
payload=json.dumps(files)
code=f'''from pathlib import Path
import json,hashlib
b=Path({B!r});files=json.loads({payload!r});xkind={kind!r};xtarget={target!r}
for n,s in files.items():
 p=b/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
if xkind=='lean':(b/'NDM_objects'/xtarget).parent.mkdir(parents=True,exist_ok=True)
pins=json.loads((b/'NDM_SOURCE_PINS.json').read_text())
for n in files:
 if n.startswith('NDM_src/'):pins[n[len('NDM_src/'):]]=hashlib.sha256((b/n).read_bytes()).hexdigest()
(b/'NDM_SOURCE_PINS.json').write_text(json.dumps(pins))
if xkind=='lean':
 cpath=b/{(a+'.json')!r};cfg=json.loads(cpath.read_text())
 for root in [b/'NDM_objects',b.parent/'codex-cx-native-front4-20261028/NDG_objects',b.parent/'codex-cx-front4-cache-20261028']:
  for p in root.rglob('*.olean'):
   cfg['deps_fingerprint']['selected_objects'][str(p)]=dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest())
 cpath.write_text(json.dumps(cfg,indent=2))
'''
r=ssh('python3',code);assert r.returncode==0,r.stdout+r.stderr
(E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
code=f'''from pathlib import Path
import json
b=Path({B!r});names={[a+'/receipt.json',a+'/stdout.log',a+'/time.log',a+'-graph-check.json',a+'-source-check.json',a+'-graph.stderr',a+'-lock-check.json','NDM_EXTRACTION_PINS.json']!r}
print(json.dumps({{n:(b/n).read_text() for n in names if (b/n).exists()}}))
'''
r=ssh('python3',code);assert r.returncode==0,r.stderr
out=json.loads(r.stdout)
for n,s in out.items():p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
assert a+'/receipt.json' in out,'no receipt; never resubmit'
rc=json.loads(out[a+'/receipt.json'])
if kind=='kani' and 'Checking harness ' in out[a+'/stdout.log']:
 assert ('Checking harness '+target+'...') in out[a+'/stdout.log'], 'own-runner harness mismatch'
 assert '1 total.' in out[a+'/stdout.log'], 'own-runner harness cardinality'

with (E/'NDM_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(rc)+'\n')
active.unlink()
print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}),flush=True)
print(out[a+'/stdout.log'][-1800:],flush=True)
