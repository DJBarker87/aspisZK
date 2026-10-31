"""Lane-owned inputs and transport; the capped host runner is unchanged."""
from pathlib import Path
from NEC_templates import template
import subprocess,json,sys,time,shlex,hashlib,os
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-slice-s-leaves-20261029';H='dombarker@100.108.41.90';C='/home/dombarker/project-offloads/codex-cx-slice-s-leaves-cache-20261029';S='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025'
a,kind,target=sys.argv[1:];prior=[json.loads(l) for l in (E/'NEC_ATTEMPTS.jsonl').read_text().splitlines() if l]
assert sum(r['kind']==kind for r in prior)<dict(lean=80,kani=80,extract=20)[kind]
assert not (E/a).exists()
def remote(code,submitted=False):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input=code,capture_output=True,text=True)
  with (E/'NEC_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=retry,submitted=submitted,exit=r.returncode,stderr=r.stderr))+'\n')
  if r.returncode!=255 or submitted:return r
  if retry<10:time.sleep(60)
 raise SystemExit('transport exhausted')
for retry in range(11):
 r=remote(f'''import pathlib,subprocess,sys
b=pathlib.Path({B!r});p=b/{(a+'-barrier-'+str(retry)+'.log')!r}
with p.open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/{(a+'-reservation.json')!r})],stdout=f,stderr=subprocess.STDOUT)
print(p.read_text());sys.exit(r.returncode)
''')
 (E/(a+f'-barrier-{retry}.log')).write_text(r.stdout+r.stderr)
 try:ad=next(json.loads(l) for l in r.stdout.splitlines() if l.startswith('{'))
 except (StopIteration,json.JSONDecodeError):
  if retry==0:time.sleep(30);continue
  raise SystemExit('STOP infrastructure: reservation JSON missing')
 (E/(a+'-admission.json')).write_text(json.dumps(dict(exit=r.returncode,reservation=ad)))
 if r.returncode==0 and ad.get('allowed') is True:break
 if (r.returncode==78 or ad.get('allowed') is False) and retry<10:print('reservation wait',flush=True);[time.sleep(60) for _ in range(3)];continue
 raise SystemExit('STOP infrastructure admission')
files={}
if kind=='lean':
 files['NEC_generated/'+target+'.lean']=(E/(target+'.lean')).read_text()
 cmd=['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NEC_generated','-o','NEC_objects/'+target+'.olean','NEC_generated/'+target+'.lean']
elif kind=='kani':
 from NEC_patch import files as native_files
 files.update({'NEC_src/'+n:v for n,v in native_files().items()})
 files.update({'NEC_gate.py':(E/'NEC_gate.py').read_text(),'NEC_graph.py':(E/'NEC_graph.py').read_text()})
 (E/a).mkdir(exist_ok=True)
 (E/a/'NEC_harness.patch').write_text((E/'NEC_native.patch').read_text())
 cmd=['python3','NEC_gate.py',a+'.json']
elif kind=='extract':
 script,ref={'NEC_EmitRef':('NEC_extract_emit.py','NEC_emit_reference'),'NEC_BindingRef':('NEC_extract_binding.py','NEC_binding_reference'),'NEC_PairRef':('NEC_extract_pair.py','NEC_pair_reference'),'NEC_ReplyRef':('NEC_extract_pure.py','NEC_pure_reference'),'NEC_LiveHeaderRef':('NEC_extract_live_header.py','NEC_live_header_reference')}.get(target,('NEC_extract.py','NEC_reference'))
 files[script]=(E/script).read_text()
 files[ref+'.rs']=template(ref)
 cmd=['python3',script]
cfg=dict(attempt=a,kind=kind,module=target,sources=list(files),command=cmd,env=dict(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',LEAN_PATH=B+'/NEC_objects:'+C+'/NDM_front4b_objects_20261029:'+C+':'+S+':'+S+'/objects'),timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,deps_fingerprint={})
if kind=='kani':
 cfg['native_command']=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+'/NEC_src/crates/aspis-statement/Cargo.toml','--target-dir',B+'/NEC_target','--lib','--features','pool-v1-kernel,pool-v1-pair-forest-active-mask-basis-audit,pool-v1-pair-forest-binary-copy-weights-audit,pool-v1-pair-forest-copy-finish-dot-basis-audit,pool-v1-pair-forest-copy-pattern-basis-audit,pool-v1-pair-forest-copy-selector-tensor-basis-audit,pool-v1-pair-forest-copy-tag-dot-basis-audit,pool-v1-pair-forest-endpoint-selector-cache-audit,pool-v1-pair-forest-packed-digest-audit,pool-v1-pair-forest-packed-digest-selector-tensor-audit,pool-v1-pair-forest-packed-range-audit,pool-v1-pair-forest-pattern-window-audit,pool-v1-pair-forest-semantic-factor-audit,r0,spend-dynamic-rate512','-j','1','-Z','unstable-options','-Z','function-contracts','-Z','stubbing','--harness-timeout','90s','--exact','--harness',target,'--output-format','terse']
 if os.environ.get('NEC_PROGRAM'):
  command=cfg['native_command'];command[command.index('--manifest-path')+1]=B+'/NEC_src/programs/r1-cost-probe/Cargo.toml'
  command[command.index('--features')+1]='pool-adapter,private-leaf-salts'
 cfg['sources']+=['NEC_SOURCE_PINS.json','NEC_src/Cargo.lock','NEC_src/Cargo.toml']
 cfg['copy_patch_sha256']='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
 cfg['expected_time']='optimized compilation then one native Box/Result selected field/call window; no arithmetic elimination'
 cfg['env'].update(CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG='0',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',RUSTFLAGS='-C link-arg=-Wl,--threads=1',TMPDIR=B+'/NEC_tmp')
 cfg['timeout']=240
if kind=='kani' and os.environ.get('NEC_TRACE'):
 cfg['trace_source_attempt']=os.environ['NEC_TRACE']
 files['NEC_trace.py']=(E/'NEC_trace.py').read_text()
 cfg['sources']+=['NEC_trace.py',cfg['trace_source_attempt']+'/receipt.json',cfg['trace_source_attempt']+'-native-pins.json']
files[a+'.json']=json.dumps(cfg)
(E/a/'sources').mkdir(parents=True)
for n,s in files.items():
 if n.startswith('NEC_src/'):continue
 p=E/a/'sources'/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
r=remote(f'''from pathlib import Path
import json,hashlib
b=Path({B!r})
for n,s in {files!r}.items():
 p=b/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
p=b/{(a+'.json')!r};cfg=json.loads(p.read_text());pins=json.loads((b/'NEC_OBJECT_PINS.json').read_text()) if cfg['kind']=='lean' else {{}}
if cfg['kind']=='lean':pins.update(json.loads((b/'NEC_SIDECAR_PINS.json').read_text()))
for q in ((b/'NEC_objects').rglob('*.olean') if cfg['kind']=='lean' else []):pins[str(q)]=dict(path=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest())
cfg['deps_fingerprint']['selected_objects']=pins
if cfg['kind']=='kani':
 source=b/'NEC_src';sp=json.loads((b/'NEC_SOURCE_PINS.json').read_text())
 for name in {files!r}:
  if name.startswith('NEC_src/'):sp[name[len('NEC_src/'):]]=hashlib.sha256((b/name).read_bytes()).hexdigest()
 (b/'NEC_SOURCE_PINS.json').write_text(json.dumps(sp,indent=1))
(b/'NEC_objects'/Path({(target+'.olean')!r})).parent.mkdir(parents=True,exist_ok=True)
p.write_text(json.dumps(cfg,indent=1))
''');assert r.returncode==0,r.stdout+r.stderr
r=remote(f'''import subprocess,sys
r=subprocess.run(['systemd-run','--user','--scope','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3','S2W_run_host.py',{(a+'.json')!r}],cwd={B!r})
sys.exit(r.returncode)
''',submitted=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
r=remote(f'''from pathlib import Path
import json
b=Path({B!r});print(json.dumps({{n:(b/n).read_text() for n in {[a+'/receipt.json',a+'/stdout.log',a+'/time.log',a+'-graph-check.json',a+'-actual-graph-check.json',a+'-actual-graph.stderr',a+'-lock-check.json',a+'-tool-pins.json',a+'-native-pins.json',a+'-properties.json',a+'-properties.stderr',a+'-trace-command.json',a+'-source-check.json',a+'-full-source-pins.json',a+'-graph.stderr','NEC_EXTRACTION_PINS.json']!r} if (b/n).exists()}}))
''');assert r.returncode==0,r.stderr
out=json.loads(r.stdout)
for n,s in out.items():p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
assert a+'/receipt.json' in out,'missing receipt; recover read-only, never resubmit'
rc=json.loads(out[a+'/receipt.json'])
summary={k:rc[k] for k in ['attempt', 'kind', 'module', 'source_revision', 'exit_status', 'wall_seconds', 'peak_rss_kib', 'swaps', 'print_axioms', 'limits', 'source_hashes']};summary.update(receipt=a+'/receipt.json',deps_fingerprint_sha256=hashlib.sha256(json.dumps(rc['deps_fingerprint'],sort_keys=True).encode()).hexdigest())
with (E/'NEC_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(summary)+'\n')
print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}));print(out[a+'/stdout.log'][-2400:])

for path in (E/a).rglob('*'):
 if path.is_file() and path.stat().st_size>20*1024*1024:
  import lzma
  raw=path.read_bytes();path.with_name(path.name+'.sha256').write_text(hashlib.sha256(raw).hexdigest()+'  '+path.name+'\n')
  path.with_name(path.name+'.xz').write_bytes(lzma.compress(raw,preset=6));path.unlink()
