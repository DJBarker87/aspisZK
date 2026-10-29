#!/usr/bin/env python3
"""One native reducer-contract attempt, using the unchanged scoped runner."""
from pathlib import Path
import hashlib,json,subprocess,sys,time,shlex
E=Path(__file__).resolve().parent;R=E.parent.parent
H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-slice-q-compose-20261029';COHERENT='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025'
a,harness,*flag=sys.argv[1:];assert a.startswith('NEB_K') and 1<=int(a[-3:])<=40
old_names=['reduce_contract','wrapper_contract','weak_contract','real_body','unimplied','frame_control']
if harness in old_names:target='field::NEB_reducer::'+harness
else:
 assert harness.startswith(('field::NEB_additive::','field::wide_exact::NEB_wide::'))
 assert all(c.isalnum() or c in '_:' for c in harness)
 target=harness
assert not (E/a).exists();active=E/'NEB_ACTIVE.json';assert not active.exists();active.write_text(json.dumps(dict(attempt=a,target=harness)))
def ssh(code,stdin=None,submitted=False):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,code],input=stdin,capture_output=True,text=True)
  with (E/'NEB_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=retry,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
  if r.returncode!=255 or submitted:return r
  if retry<10:time.sleep(60)
 raise SystemExit('transport exhausted')
for retry in range(11):
 code=f'''import pathlib,subprocess,json,sys
b=pathlib.Path({B!r});log=b/{(a+'-barrier-'+str(retry)+'.log')!r}
with log.open('w') as f:r=subprocess.run(['python3',{COHERENT!r}+'/JFz_reservation.py',str(b/{(a+'-admission.json')!r})],stdout=f,stderr=subprocess.STDOUT)
print(log.read_text());sys.exit(r.returncode)
'''
 r=ssh('python3',code);(E/(a+f'-barrier-{retry}.log')).write_text(r.stdout+r.stderr)
 try:ad=next(json.loads(l) for l in r.stdout.splitlines() if l.startswith('{'))
 except (StopIteration,json.JSONDecodeError):
  if retry==0:time.sleep(30);continue
  raise SystemExit('STOP infrastructure: missing admission JSON')
 (E/(a+'-admission.json')).write_text(json.dumps(dict(exit_status=r.returncode,reservation=ad),indent=1)+'\n')
 if r.returncode==0 and ad.get('allowed') is True:break
 if (r.returncode==78 or ad.get('allowed') is False) and retry<10:print('reservation refused; wait three minutes',flush=True);time.sleep(180);continue
 raise SystemExit('STOP infrastructure admission')
ni=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+'/NEB_src/crates/aspis-core/Cargo.toml','--target-dir',B+'/NEB_target','--features','r0','--lib','-j','1','-Z','unstable-options','-Z','function-contracts','-Z','stubbing','--harness-timeout','90s','--exact','--harness',target,'--output-format','terse']
env=dict(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG='0',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',RUSTFLAGS='-C link-arg=-Wl,--threads=1',TMPDIR=B+'/NEB_tmp')
if flag:
 assert len(flag)==1 and flag[0] in ['NEB_wrong_reduce','NEB_wrong_wrapper']+['NEB_wrong_'+p+'_'+o for p in ['m','c','q','e'] for o in ['add','sub','double']]+['NEB_wrong_limbs','NEB_wrong_canonical','NEB_wrong_embed'];env['RUSTFLAGS']+=' --cfg '+flag[0]
sources=['NEB_TOOL_PINS.json','NEB_gate.py','NEB_graph.py','NEB_SOURCE_PINS.json','NEB_src/Cargo.lock','NEB_src/Cargo.toml','NEB_src/crates/aspis-core/src/field.rs','NEB_src/crates/aspis-core/src/field/NEB_reducer.rs','NEB_src/crates/aspis-core/src/lib.rs','NEB_src/crates/aspis-core/src/field/wide_exact.rs','NEB_src/crates/aspis-core/src/field/NEB_additive.rs','NEB_src/crates/aspis-core/src/field/NEB_additive_reference.rs','NEB_src/crates/aspis-core/src/field/wide_exact/NEB_wide.rs']
cfg=dict(attempt=a,kind='kani',target=target,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),source_tree_dirty=True,sources=sources,command=['python3','NEB_gate.py',a+'.json'],native_command=ni,timeout=180,env=env,deps_fingerprint=dict(source_pinset='NEB_SOURCE_PINS.json',frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'),expected_time='Optimized compilation then one named scalar or fixed-record/array contract; no field multiplication, generation or elimination',copy_patch_sha256=hashlib.sha256((E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch').read_bytes()).hexdigest(),feature_scope='core r0 helper, feature-independent frozen method bodies; cfg(kani) instrumentation only',copy_dependency='KMX-approved copy implementation applied; scalar-only reducer has no copy dependence, record/array lanes require matched KMX positive/negative controls')
(E/(a+'.json')).write_text(json.dumps(cfg,indent=1)+'\n')
files={'NEB_TOOL_PINS.json':(E/'NEB_TOOL_PINS.json').read_text(),'NEB_gate.py':(E/'NEB_gate.py').read_text(),'NEB_graph.py':(E/'NEB_graph.py').read_text(),a+'.json':json.dumps(cfg)}
r=ssh('python3',f'''from pathlib import Path
import json
b=Path({B!r})
for n,s in json.loads({json.dumps(files)!r}).items():(b/n).write_text(s)
''');assert r.returncode==0,r.stderr
r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
names=[a+'/receipt.json',a+'/stdout.log',a+'/time.log',a+'-graph-check.json',a+'-graph.stderr',a+'-lock-check.json',a+'-source-check.json',a+'-tool-check.json',a+'/sources/NEB_gate.py',a+'/sources/NEB_graph.py']
r=ssh('python3',f'''from pathlib import Path
import json
b=Path({B!r});print(json.dumps({{n:(b/n).read_text() for n in {names!r} if (b/n).exists()}}))
''');assert r.returncode==0,r.stderr
out=json.loads(r.stdout)
for n,s in out.items():p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
assert a+'/receipt.json' in out,'submitted attempt unresolved; recover read-only, never resubmit'
rc=json.loads(out[a+'/receipt.json'])
with (E/'NEB_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(rc)+'\n')
active.unlink()
print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps']}),flush=True);print('\n'.join(line for line in out[a+'/stdout.log'].splitlines() if any(t in line for t in ['Checking harness','VERIFICATION','failed (','Failed Checks:','error:','Verification Time:'])),flush=True)
if rc['exit_status'] in [124,137] or 'timed out' in out[a+'/stdout.log'].lower():raise SystemExit('STOP timed-out shape; isolate and split, never rerun unchanged')
sys.exit(rc['exit_status'])
