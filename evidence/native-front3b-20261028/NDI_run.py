"""Lane-owned serial wrapper around unchanged S2W launchers."""
from pathlib import Path
import subprocess,json,sys,time,shlex,hashlib,os
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-native-front3b-20261028';H='dombarker@100.108.41.90'
a,kind,target=sys.argv[1:];limit=80 if kind=='kani' else (20 if kind=='extract' else 80)
assert int(a[-3:])<=limit
assert not (E/a).exists()
active=E/'NDI_ACTIVE.json';assert not active.exists(),active
active.write_text(json.dumps(dict(attempt=a)))
def ssh(code,stdin=None,submitted=False):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2',H,code],input=stdin,capture_output=True,text=True)
  with (E/'NDI_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=retry,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
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
files={'NDI_gate.py':(E/'NDI_gate.py').read_text()}
if kind=='kani':
 from NDI_patch import files as patch_files
 for n,s in patch_files().items():files['NDI_src/'+n]=s
 sources=['NDI_gate.py','NDI_SOURCE_PINS.json']+list(n for n in files if n.endswith('.rs'))+['NDI_src/Cargo.lock','NDI_src/Cargo.toml','NDI_src/crates/aspis-r1-cost-probe/src/r1_wire.rs','NDI_src/crates/aspis-r1-cost-probe/src/compact.rs','NDI_src/crates/aspis-r1-cost-probe/src/lib.rs','NDI_src/crates/aspis-r1-cost-probe/src/candidate.rs','NDI_src/crates/aspis-r1-cost-probe/src/verifier.rs','NDI_src/KMX_stubs.rs','NDI_src/KMX_native.rs','NDI_src/KMX_CopyMeaning.lean']
 native=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+'/NDI_src/crates/aspis-r1-cost-probe/Cargo.toml','--target-dir',B+'/NDI_target','--features','private-leaf-salts,optimized-terminal,program-build','--lib','-j','1','-Z','unstable-options','-Z','function-contracts','-Z','stubbing','--harness-timeout','90s','--exact','--harness',target,'--output-format','terse']
 command=['python3','NDI_gate.py',a+'.json']
elif kind=='extract':
 files['NDI_extract.py']=(E/'NDI_extract.py').read_text();sources=['NDI_extract.py','NDI_src/crates/aspis-r1-cost-probe/src/NDI_reference.rs'];native=[];command=['python3','NDI_extract.py']
else:
 files['NDI_generated/'+target+'.lean']=(E/(target+'.lean')).read_text();sources=['NDI_generated/'+target+'.lean']
 native=[];command=['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NDI_generated','-o','NDI_objects/'+target+'.olean',sources[0]]
env=dict(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG='0',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',RUSTFLAGS='-C link-arg=-Wl,--threads=1',TMPDIR=B+'/NDI_tmp',LEAN_PATH=B+'/NDI_objects:/home/dombarker/project-offloads/codex-cx-native-front3-20261028/NDF_objects:/home/dombarker/project-offloads/codex-cx-front3-cache-20261028/NCO_objects:/home/dombarker/project-offloads/codex-cx-front3-cache-20261028:/home/dombarker/project-offloads/codex-cx-sound-int2-20261025:/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects')
if os.environ.get('NDI_EXTRACT_PARSER'):env['NDI_EXTRACT_PARSER']=os.environ['NDI_EXTRACT_PARSER']
if os.environ.get('NDI_PROGRAM'):
 native[native.index('--manifest-path')+1]=B+'/NDI_src/programs/r1-cost-probe/Cargo.toml'
 native[native.index('--features')+1]='pool-adapter,private-leaf-salts'
 env['NDI_PROGRAM']='1'
if os.environ.get('NDI_RUST_CFG'):env['RUSTFLAGS']+=' --cfg '+os.environ['NDI_RUST_CFG']
cfg=dict(attempt=a,kind=kind,module=target,sources=sources,command=command,native_command=native,env=env,timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,deps_fingerprint={'source_pinset':'NDI_SOURCE.json','library_pinset':'NDI_SOURCE.json:library'},expected_time='optimized compile then one contract/shape proof; no field multiplication',copy_patch_sha256='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67')
if kind=='lean':
 cfg['deps_fingerprint']['selected_objects']=dict(json.loads((E/'NDI_SOURCE.json').read_text())['inherited_object_pins']['selected_objects'])
 for old,v in json.loads((E/'NDI_SOURCE.json').read_text())['cache_imports'].items():
  if '/NCO_objects/' in old:
   dest='/home/dombarker/project-offloads/codex-cx-front3-cache-20261028/NCO_objects/'+old.split('/NCO_objects/',1)[1]
   cfg['deps_fingerprint']['selected_objects'][dest]=dict(path=dest,sha256=v['selected_sha256'])
 if target=='NDI_Audit':
  cfg['deps_fingerprint']['selected_objects']=json.loads((E/'NDI_AUDIT_PINS.json').read_text())['selected_objects']
  files['NDI_AUDIT_PINS.json']=(E/'NDI_AUDIT_PINS.json').read_text()
  sources.append('NDI_AUDIT_PINS.json')
files[a+'.json']=json.dumps(cfg,indent=2)
# Upload after admission; snapshots permit exact local reconstruction.
for n,s in files.items():
 p=E/a/'sources'/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
payload=json.dumps(files)
code=f'''from pathlib import Path
import json,hashlib
b=Path({B!r});files=json.loads({payload!r});xkind={kind!r};xtarget={target!r}
for n,s in files.items():
 p=b/n;p.parent.mkdir(parents=True,exist_ok=True)
 if p.is_symlink():p.unlink()
 p.write_text(s)
if xkind=='lean':
 (b/'NDI_objects'/xtarget).parent.mkdir(parents=True,exist_ok=True)
 (b/'NDI_tmp').mkdir(exist_ok=True)
pins=json.loads((b/'NDI_SOURCE_PINS.json').read_text())
for n in files:
 if n.startswith('NDI_src/'):pins[n[len('NDI_src/'):]]=hashlib.sha256((b/n).read_bytes()).hexdigest()
(b/'NDI_SOURCE_PINS.json').write_text(json.dumps(pins))
'''
r=ssh('python3',code);assert r.returncode==0,r.stdout+r.stderr
(E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
code=f'''from pathlib import Path
import json
b=Path({B!r});names={[a+'/receipt.json',a+'/stdout.log',a+'/time.log',a+'-graph-check.json',a+'-source-check.json',a+'-graph.stderr',a+'-lock-check.json','NDI_EXTRACTION_PINS.json']!r}
print(json.dumps({{n:(b/n).read_text() for n in names if (b/n).exists()}}))
'''
r=ssh('python3',code);assert r.returncode==0,r.stderr
out=json.loads(r.stdout)
for n,s in out.items():p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
assert a+'/receipt.json' in out,'no receipt; never resubmit'
rc=json.loads(out[a+'/receipt.json'])
with (E/'NDI_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(rc)+'\n')
active.unlink()
print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}),flush=True)
print(out[a+'/stdout.log'][-1800:],flush=True)
