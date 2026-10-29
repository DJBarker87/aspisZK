import sys
sys.dont_write_bytecode=True
from NDL_sources import source
from NDL_journal import entry
import sys
sys.dont_write_bytecode=True
"""Lane-owned serial wrapper around unchanged S2W launchers."""
from pathlib import Path
import subprocess,json,sys,time,shlex,hashlib,os
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-native-front1b-20261028';H='dombarker@100.108.41.90'
a,kind,target=sys.argv[1:];limit=80 if kind!='extract' else 20
assert int(a[-3:])<=limit
assert not (E/a).exists()
active=E/'NDL_ACTIVE.json';assert not active.exists(),active
active.write_text(json.dumps(dict(attempt=a)))
def ssh(code,stdin=None,submitted=False):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2',H,code],input=stdin,capture_output=True,text=True)
  with (E/'NDL_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=retry,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
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
files={'NDL_gate.py':(E/'NDL_gate.py').read_text()}
if kind=='kani':
 sources=['NDL_gate.py','NDL_SOURCE_PINS.json','NDL_src/Cargo.lock','NDL_src/crates/aspis-core/src/field.rs','NDL_src/crates/aspis-core/src/field/NDD_field.rs','NDL_src/crates/aspis-core/src/field/NDL_core.rs','NDL_src/crates/aspis-core/src/field/NDL_core_reference.rs']
 native=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+'/NDL_src/crates/aspis-core/Cargo.toml','--target-dir',B+'/NDL_target','--features','r0','--lib','-j','1','-Z','unstable-options','-Z','function-contracts','-Z','stubbing','--harness-timeout','90s','--exact','--harness',target,'--output-format','terse']
 command=['python3','NDL_gate.py',a+'.json']
 if os.environ.get('NDL_PACKAGE')=='verifier':
  native[native.index('--manifest-path')+1]=B+'/NDL_src/crates/aspis-r1-cost-probe/Cargo.toml'
  native[native.index('--features')+1]='private-leaf-salts,optimized-terminal,program-build'
  sources+=['NDL_src/crates/aspis-r1-cost-probe/src/multiproof.rs','NDL_src/crates/aspis-r1-cost-probe/src/NDD_multiproof.rs','NDL_src/crates/aspis-r1-cost-probe/src/weights.rs','NDL_src/crates/aspis-r1-cost-probe/src/NDL_weights.rs','NDL_src/crates/aspis-r1-cost-probe/src/NDL_reference.rs','NDL_src/crates/aspis-r1-cost-probe/src/fast_pairing.rs','NDL_src/crates/aspis-r1-cost-probe/src/NDL_pairing.rs','NDL_src/crates/aspis-r1-cost-probe/src/NDL_dot.rs','NDL_src/crates/aspis-core/src/field/NDL_core.rs']

elif kind=='extract':
 files['NDL_extract.py']=(E/'NDL_extract.py').read_text();files['NDL_reference.rs']=source('NDL_reference.rs');sources=['NDL_extract.py','NDL_reference.rs'];native=[];command=['python3','NDL_extract.py']
else:
 files['NDL_generated/'+target+'.lean']=(E/(target+'.lean')).read_text() if (E/(target+'.lean')).exists() else Path('lean',target+'.lean').read_text();sources=['NDL_generated/'+target+'.lean']
 native=[];command=['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NDL_generated','-o','NDL_objects/'+target+'.olean',sources[0]]
env=dict(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG='0',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',RUSTFLAGS='-C link-arg=-Wl,--threads=1',TMPDIR=B+'/NDL_tmp',LEAN_PATH=B+'/NDL_objects:/home/dombarker/project-offloads/codex-cx-front1-cache-20261028:/home/dombarker/project-offloads/codex-cx-sound-int2-20261025:/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects')
if os.environ.get('NDL_EXTRACT_CONFIG'):env['NDL_EXTRACT_CONFIG']=os.environ['NDL_EXTRACT_CONFIG']
if os.environ.get('NDL_SCALAR_EXTRACT'):env['NDL_SCALAR_EXTRACT']=os.environ['NDL_SCALAR_EXTRACT']
if os.environ.get('NDL_FIELD_EXTRACT'):env['NDL_FIELD_EXTRACT']=os.environ['NDL_FIELD_EXTRACT']
if os.environ.get('NDL_EXTRACT_PARSER'):env['NDL_EXTRACT_PARSER']=os.environ['NDL_EXTRACT_PARSER']
if os.environ.get('NDL_RUST_CFG'):env['RUSTFLAGS']+=' --cfg '+os.environ['NDL_RUST_CFG']
cfg=dict(attempt=a,kind=kind,module=target,sources=sources,command=command,native_command=native,env=env,timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,deps_fingerprint={'source_pinset':'NDL_SOURCE.json','library_pinset':'NDL_SOURCE.json:library'},expected_time='optimized compile then one contract/shape proof; no field multiplication',copy_patch_sha256='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67')
if kind=='lean':
 cfg['expected_time']='Focused Lean elaboration and standard-axiom audit against pinned objects'
 cfg['deps_fingerprint']['selected_objects']={p:dict(path=p,sha256=h) for p,h in json.loads((E/'NDL_SOURCE.json').read_text())['library'].items()}
 if True:
  cfg['deps_fingerprint']['selected_objects']=json.loads((E/'NDL_AUDIT_PINS.json').read_text())['selected_objects']
  files['NDL_AUDIT_PINS.json']=(E/'NDL_AUDIT_PINS.json').read_text()
  sources.append('NDL_AUDIT_PINS.json')
if kind=='lean':
 r=ssh('python3',f'''from pathlib import Path
import json,hashlib
b=Path({B!r})/'NDL_objects'
print(json.dumps({{str(p):dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size) for p in b.rglob('*.olean') if p.is_file()}}))
''')
 assert r.returncode==0,r.stderr
 cfg['deps_fingerprint']['selected_objects'].update(json.loads(r.stdout))
if kind=='lean' and os.environ.get('NDL_DEPS_ONLY')=='1':
 cfg['command']=['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','lean','--deps',sources[0]]
 cfg['expected_time']='Read-only Lean object-resolution inspection; no theorem or object emitted'
files[a+'.json']=json.dumps(cfg,indent=2)
# Upload after admission; snapshots permit exact local reconstruction.
for n,s in files.items():
 p=E/a/'sources'/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
payload=json.dumps(files)
code=f'''from pathlib import Path
import json,hashlib
b=Path({B!r});files=json.loads({payload!r});xkind={kind!r};xtarget={target!r}
for n,s in files.items():
 p=b/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
if xkind=='lean':(b/'NDL_objects'/xtarget).parent.mkdir(parents=True,exist_ok=True)
pins=json.loads((b/'NDL_SOURCE_PINS.json').read_text())
for n in files:
 if n.startswith('NDL_src/'):pins[n[len('NDL_src/'):]]=hashlib.sha256((b/n).read_bytes()).hexdigest()
(b/'NDL_SOURCE_PINS.json').write_text(json.dumps(pins))
'''
r=ssh('python3',code);assert r.returncode==0,r.stdout+r.stderr
(E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
code=f'''from pathlib import Path
import json
b=Path({B!r});names={[a+'/receipt.json',a+'/stdout.log',a+'/time.log',a+'-graph-check.json',a+'-source-check.json',a+'-graph.stderr',a+'-lock-check.json','NDL_EXTRACTION_PINS.json']!r}
print(json.dumps({{n:(b/n).read_text() for n in names if (b/n).exists()}}))
'''
r=ssh('python3',code);assert r.returncode==0,r.stderr
out=json.loads(r.stdout)
for n,s in out.items():p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
assert a+'/receipt.json' in out,'no receipt; never resubmit'
rc=json.loads(out[a+'/receipt.json'])
with (E/'NDL_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(entry(rc))+'\n')
active.unlink()
print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}),flush=True)
print(out[a+'/stdout.log'][-700:],flush=True)

# Do not treat timed-out verification as a completed proof batch.
if 'timed out' in out[a+'/stdout.log'].lower() or rc['exit_status'] in [124,137]:
 raise SystemExit('STOP shape: split this timed-out/killed proof before continuing')
