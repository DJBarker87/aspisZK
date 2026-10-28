"""Lane-owned serial wrapper around unchanged S2W launchers."""
from pathlib import Path
import subprocess,json,sys,time,shlex,hashlib,os
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-native-front2-20261028';H='dombarker@100.108.41.90'
a,kind,target=sys.argv[1:];limit=80
assert int(a[-3:]) <= (20 if kind=='extract' else limit)
assert not (E/a).exists()
active=E/'NDE_ACTIVE.json';assert not active.exists(),active
active.write_text(json.dumps(dict(attempt=a)))
def ssh(code,stdin=None,submitted=False):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2',H,code],input=stdin,capture_output=True,text=True)
  with (E/'NDE_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=retry,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
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
files={'NDE_gate.py':(E/'NDE_gate.py').read_text()}
if kind=='kani':
 from NDE_patch import files as patch_files
 for n,s in patch_files().items():files['NDE_src/'+n]=s
 sources=['NDE_gate.py','NDE_SOURCE_PINS.json']+list(n for n in files if n.endswith('.rs'))+['NDE_src/Cargo.lock','NDE_src/Cargo.toml']
 native=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+'/NDE_src/crates/aspis-statement/Cargo.toml','--target-dir',B+'/NDE_target','--features','r0,pool-v1-kernel,pool-v1-pair-forest-packed-digest-selector-tensor-audit,pool-v1-pair-forest-binary-copy-weights-audit,pool-v1-pair-forest-endpoint-selector-cache-audit,pool-v1-pair-forest-semantic-factor-audit,pool-v1-pair-forest-pattern-window-audit,pool-v1-pair-forest-copy-tag-dot-basis-audit,pool-v1-pair-forest-copy-finish-dot-basis-audit,pool-v1-pair-forest-packed-range-audit,pool-v1-pair-forest-active-mask-basis-audit','--lib','-j','1','-Z','unstable-options','-Z','function-contracts','-Z','stubbing','--harness-timeout','90s','--exact','--harness',target,'--output-format','terse']
 command=['python3','NDE_gate.py',a+'.json']
elif kind=='extract':
 files['NDE_extract.py']=(E/'NDE_extract.py').read_text();files['NDE_reference.rs']=(E/'NDE_reference.rs').read_text();sources=['NDE_extract.py','NDE_reference.rs'];native=[];command=['python3','NDE_extract.py']
else:
 files['NDE_generated/'+target+'.lean']=(E/(target+'.lean')).read_text();sources=['NDE_generated/'+target+'.lean']
 native=[];command=['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NDE_generated','-o','NDE_objects/'+target+'.olean',sources[0]]
env=dict(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG='0',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',RUSTFLAGS='-C link-arg=-Wl,--threads=1',TMPDIR=B+'/NDE_tmp',LEAN_PATH=B+'/NDE_objects:/home/dombarker/project-offloads/codex-cx-front2-cache-20261028:/home/dombarker/project-offloads/codex-cx-sound-int2-20261025:/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects')
env['LEAN_PATH'] += ':' + '/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean:/home/dombarker/project-offloads/codex-cx-replay-dry-20261026/RPx_overlay:/home/dombarker/project-offloads/codex-cx-replay-dry-20261026/RPv_overlay:/home/dombarker/project-offloads/codex-cx-replay-dry-20261026/RPu_overlay:/home/dombarker/project-offloads/codex-cx-replay-dry-20261026/RPt_overlay:/home/dombarker/project-offloads/codex-cx-replay-dry-20261026/RPz8_overlay:/home/dombarker/project-offloads/codex-cx-replay-dry-20261026/RPz7_overlay:/home/dombarker/project-offloads/codex-cx-replay-dry-20261026/RPz4_trusted:/home/dombarker/project-offloads/codex-cx-replay-dry-20261026/RPz_trusted'
if os.environ.get('NDE_EXTRACT_PARSER'):env['NDE_EXTRACT_PARSER']=os.environ['NDE_EXTRACT_PARSER']
if os.environ.get('NDE_RUST_CFG'):env['RUSTFLAGS']+=' --cfg '+os.environ['NDE_RUST_CFG']
cfg=dict(attempt=a,kind=kind,module=target,sources=sources,command=command,native_command=native,env=env,timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,deps_fingerprint={'source_pinset':'NDE_SOURCE.json','library_pinset':'NDE_SOURCE.json:library'},expected_time='optimized compile then one contract/shape proof; no field multiplication',copy_patch_sha256='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67')
if kind=='lean':
 cfg['deps_fingerprint']['selected_objects']={p:dict(path=p,sha256=h) for p,h in json.loads((E/'NDE_SOURCE.json').read_text())['library'].items()}
 cfg['deps_fingerprint']['selected_objects'].update(json.loads((E/'NDE_COHORT_PINS.json').read_text()))
 if target=='NDE_Audit':
  cfg['deps_fingerprint']['selected_objects']=json.loads((E/'NDE_AUDIT_PINS.json').read_text())['selected_objects']
  files['NDE_AUDIT_PINS.json']=(E/'NDE_AUDIT_PINS.json').read_text()
  sources.append('NDE_AUDIT_PINS.json')
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
if xkind=='lean':(b/'NDE_objects'/xtarget).parent.mkdir(parents=True,exist_ok=True)
pins=json.loads((b/'NDE_SOURCE_PINS.json').read_text())
for n in files:
 if n.startswith('NDE_src/'):pins[n[len('NDE_src/'):]]=hashlib.sha256((b/n).read_bytes()).hexdigest()
(b/'NDE_SOURCE_PINS.json').write_text(json.dumps(pins))
'''
r=ssh('python3',code);assert r.returncode==0,r.stdout+r.stderr
(E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
code=f'''from pathlib import Path
import json
b=Path({B!r});names={[a+'/receipt.json',a+'/stdout.log',a+'/time.log',a+'-graph-check.json',a+'-source-check.json',a+'-graph.stderr',a+'-lock-check.json','NDE_EXTRACTION_PINS.json','NDE_extracted/NDE_Reference/Types.lean','NDE_extracted/NDE_Reference/Funs.lean','NDE_extracted2/NDE_Reference2/Types.lean','NDE_extracted2/NDE_Reference2/Funs.lean','NDE_extracted3/NDE_Reference3/Types.lean','NDE_extracted3/NDE_Reference3/Funs.lean','NDE_extracted4/NDE_Reference4/Types.lean','NDE_extracted4/NDE_Reference4/Funs.lean','NDE_extracted5/NDE_Reference5/Types.lean','NDE_extracted5/NDE_Reference5/Funs.lean']!r}
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
with (E/'NDE_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(summary)+'\n')
active.unlink()
print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}),flush=True)
print(out[a+'/stdout.log'][-1800:],flush=True)
