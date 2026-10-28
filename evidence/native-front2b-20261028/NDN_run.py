"""Lane-owned serial wrapper around unchanged S2W launchers."""
from pathlib import Path
import subprocess,json,sys,time,shlex,hashlib,os
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-native-front2b-20261028';H='dombarker@100.108.41.90'
a,kind,target=sys.argv[1:];limit=80
assert int(a[-3:]) <= (20 if kind=='extract' else limit)
assert not (E/a).exists()
active=E/'NDN_ACTIVE.json';assert not active.exists(),active
active.write_text(json.dumps(dict(attempt=a)))
def ssh(code,stdin=None,submitted=False):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2',H,code],input=stdin,capture_output=True,text=True)
  with (E/'NDN_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=retry,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
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
files={'NDN_gate.py':(E/'NDN_gate.py').read_text()}
if kind=='kani':
 from NDN_patch import files as patch_files
 for n,s in patch_files().items():files['NDN_src/'+n]=s
 sources=['NDN_gate.py','NDN_SOURCE_PINS.json']+list(n for n in files if n.endswith('.rs'))+['NDN_src/Cargo.lock','NDN_src/Cargo.toml']
 native=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+'/NDN_src/crates/aspis-statement/Cargo.toml','--target-dir',B+'/NDN_target','--features','r0,pool-v1-kernel,pool-v1-pair-forest-packed-digest-selector-tensor-audit,pool-v1-pair-forest-binary-copy-weights-audit,pool-v1-pair-forest-endpoint-selector-cache-audit,pool-v1-pair-forest-semantic-factor-audit,pool-v1-pair-forest-pattern-window-audit,pool-v1-pair-forest-copy-tag-dot-basis-audit,pool-v1-pair-forest-copy-finish-dot-basis-audit,pool-v1-pair-forest-packed-range-audit,pool-v1-pair-forest-active-mask-basis-audit','--lib','-j','1','-Z','unstable-options','-Z','function-contracts','-Z','stubbing','--harness-timeout','90s','--exact','--harness',target,'--output-format','terse']
 command=['python3','NDN_gate.py',a+'.json']
elif kind=='extract':
 files['NDN_EXTRACT_JOBS.json']=(E/'NDN_EXTRACT_JOBS.json').read_text();files['NDN_extract.py']=(E/'NDN_extract.py').read_text();files['NDN_reference.rs']=(E/'NDN_reference.rs').read_text();sources=['NDN_extract.py','NDN_reference.rs','NDN_EXTRACT_JOBS.json'];native=[];command=['python3','NDN_extract.py']
else:
 source_file=E/(target+'.lean')
 if target.startswith('NDE_Reference14/'):
  source_file=E.parent/'native-front2-20261028'/'NDE_extracted14'/(target+'.lean')
 files['NDN_generated/'+target+'.lean']=source_file.read_text();sources=['NDN_generated/'+target+'.lean']
 native=[];command=['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NDN_generated','-o','NDN_objects/'+target+'.olean',sources[0]]
env=dict(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG='0',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',RUSTFLAGS='-C link-arg=-Wl,--threads=1',TMPDIR=B+'/NDN_tmp',LEAN_PATH=B+'/NDN_objects:/home/dombarker/project-offloads/codex-cx-front2-cache-20261028:/home/dombarker/project-offloads/codex-cx-sound-int2-20261025:/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects')
env['LEAN_PATH'] += ':/home/dombarker/project-offloads/codex-cx-native-front2-20261028/NDE_objects'
env['LEAN_PATH'] += ':' + '/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean:/home/dombarker/project-offloads/codex-cx-replay-dry-20261026/RPx_overlay:/home/dombarker/project-offloads/codex-cx-replay-dry-20261026/RPv_overlay:/home/dombarker/project-offloads/codex-cx-replay-dry-20261026/RPu_overlay:/home/dombarker/project-offloads/codex-cx-replay-dry-20261026/RPt_overlay:/home/dombarker/project-offloads/codex-cx-replay-dry-20261026/RPz8_overlay:/home/dombarker/project-offloads/codex-cx-replay-dry-20261026/RPz7_overlay:/home/dombarker/project-offloads/codex-cx-replay-dry-20261026/RPz4_trusted:/home/dombarker/project-offloads/codex-cx-replay-dry-20261026/RPz_trusted'
if os.environ.get('NDN_EXTRACT_PARSER'):env['NDN_EXTRACT_PARSER']=os.environ['NDN_EXTRACT_PARSER']
if os.environ.get('NDN_RUST_CFG'):env['RUSTFLAGS']+=' --cfg '+os.environ['NDN_RUST_CFG']
cfg=dict(attempt=a,kind=kind,module=target,sources=sources,command=command,native_command=native,env=env,timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,deps_fingerprint={'source_pinset':'NDN_SOURCE.json','library_pinset':'NDN_SOURCE.json:library'},expected_time='optimized compile then one contract/shape proof; no field multiplication',copy_patch_sha256='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67')
if kind=='extract':cfg['expected_time']='optimized Rust compilation followed by pinned Charon/Aeneas reference extraction; no native proof execution'
if kind=='lean':
 cfg['expected_time']='focused symbolic Lean module typecheck and requested axioms print; no manifest replay'
 cfg['deps_fingerprint']['selected_objects']={p:dict(path=p,sha256=h) for p,h in json.loads((E/'NDN_SOURCE.json').read_text())['library'].items()}
 cfg['deps_fingerprint']['selected_objects'].update(json.loads((E/'NDN_COHORT_PINS.json').read_text()))
 code=f"from pathlib import Path;import json,hashlib;b=Path({B!r})/'NDN_objects';print(json.dumps({{str(p):dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in b.rglob('*.olean')}}))"
 pinned=ssh('python3 -c '+shlex.quote(code));assert pinned.returncode==0,pinned.stderr
 cfg['deps_fingerprint']['selected_objects'].update(json.loads(pinned.stdout))
 if target=='NDN_Audit':
  cfg['deps_fingerprint']['selected_objects']=json.loads((E/'NDN_AUDIT_PINS.json').read_text())['selected_objects']
  files['NDN_AUDIT_PINS.json']=(E/'NDN_AUDIT_PINS.json').read_text()
  sources.append('NDN_AUDIT_PINS.json')
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
if xkind=='lean':(b/'NDN_objects'/xtarget).parent.mkdir(parents=True,exist_ok=True)
pins=json.loads((b/'NDN_SOURCE_PINS.json').read_text())
for n in files:
 if n.startswith('NDN_src/'):pins[n[len('NDN_src/'):]]=hashlib.sha256((b/n).read_bytes()).hexdigest()
(b/'NDN_SOURCE_PINS.json').write_text(json.dumps(pins))
'''
r=ssh('python3',code);assert r.returncode==0,r.stdout+r.stderr
(E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
code=f'''from pathlib import Path
import json
b=Path({B!r});names={[a+'/receipt.json',a+'/stdout.log',a+'/time.log',a+'-graph-check.json',a+'-source-check.json',a+'-graph.stderr',a+'-lock-check.json','NDN_EXTRACTION_PINS.json','NDN_extracted1/NDN_Reference1/Types.lean','NDN_extracted1/NDN_Reference1/Funs.lean','NDN_extracted2/NDN_Reference2/Types.lean','NDN_extracted2/NDN_Reference2/Funs.lean','NDN_extracted3/NDN_Reference3/Types.lean','NDN_extracted3/NDN_Reference3/Funs.lean','NDN_extracted4/NDN_Reference4/Types.lean','NDN_extracted4/NDN_Reference4/Funs.lean','NDN_extracted5/NDN_Reference5/Types.lean','NDN_extracted5/NDN_Reference5/Funs.lean','NDN_extracted6/NDN_Reference6/Types.lean','NDN_extracted6/NDN_Reference6/Funs.lean','NDN_extracted7/NDN_Reference7/Types.lean','NDN_extracted7/NDN_Reference7/Funs.lean','NDN_extracted8/NDN_Reference8/Types.lean','NDN_extracted8/NDN_Reference8/Funs.lean','NDN_extracted9/NDN_Reference9/Types.lean','NDN_extracted9/NDN_Reference9/Funs.lean','NDN_extracted10/NDN_Reference10/Types.lean','NDN_extracted10/NDN_Reference10/Funs.lean','NDN_extracted11/NDN_Reference11/Types.lean','NDN_extracted11/NDN_Reference11/Funs.lean','NDN_extracted12/NDN_Reference12/Types.lean','NDN_extracted12/NDN_Reference12/Funs.lean','NDN_extracted13/NDN_Reference13/Types.lean','NDN_extracted13/NDN_Reference13/Funs.lean','NDN_extracted14/NDN_Reference14/Types.lean','NDN_extracted14/NDN_Reference14/Funs.lean','NDN_extracted15/NDN_Reference15/Types.lean','NDN_extracted15/NDN_Reference15/Funs.lean','NDN_extracted16/NDN_Reference16/Types.lean','NDN_extracted16/NDN_Reference16/Funs.lean','NDN_extracted17/NDN_Reference17/Types.lean','NDN_extracted17/NDN_Reference17/Funs.lean','NDN_extracted18/NDN_Reference18/Types.lean','NDN_extracted18/NDN_Reference18/Funs.lean','NDN_extracted19/NDN_Reference19/Types.lean','NDN_extracted19/NDN_Reference19/Funs.lean','NDN_extracted20/NDN_Reference20/Types.lean','NDN_extracted20/NDN_Reference20/Funs.lean']!r}
print(json.dumps({{n:(b/n).read_text() for n in names if (b/n).exists()}}))
'''
r=ssh('python3',code);assert r.returncode==0,r.stderr
out=json.loads(r.stdout)
for n,s in out.items():p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
assert a+'/receipt.json' in out,'no receipt; never resubmit'
rc=json.loads(out[a+'/receipt.json'])
summary=json.loads(json.dumps(rc))
selected=summary.get('deps_fingerprint',{}).pop('selected_objects',None)
if selected:summary['deps_fingerprint']['selected_objects_summary']=dict(count=len(selected),sha256=hashlib.sha256(json.dumps(selected,sort_keys=True).encode()).hexdigest(),full_receipt=a+'/receipt.json')
with (E/'NDN_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(summary)+'\n')
active.unlink()
print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}),flush=True)
print(out[a+'/stdout.log'][-1800:],flush=True)
