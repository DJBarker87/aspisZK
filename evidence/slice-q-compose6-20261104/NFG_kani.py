#!/usr/bin/env python3
"""One native fixed-value/caller-cut attempt, using the unchanged scoped runner."""
from pathlib import Path
import hashlib,json,subprocess,sys,time,shlex
E=Path(__file__).resolve().parent;R=E.parent.parent
H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-slice-q-compose6-20261104';COHERENT='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025'
a,harness,*flag=sys.argv[1:];assert a.startswith('NFG_K') and 1<=int(a[-3:])<=999
assert sum(json.loads(p.read_text()).get('kind')=='kani' for p in E.glob('NFG_K*/receipt.json'))<110,'Kani run budget exhausted'
assert harness.startswith(('verifier::NFG_inverse::','verifier::candidate::NFG_loop::'))
assert all(c.isalnum() or c in '_:' for c in harness)
target=harness
if harness.startswith(('verifier::NFG_inverse::','verifier::candidate::NFG_loop::')):
 text=(E/('NFG_inverse.rs.txt' if '::NFG_inverse::' in harness else 'NFG_loop.rs.txt')).read_text()
 for f in flag:assert f in text,('cfg flag absent from selected source',f)
assert not (E/a).exists();active=E/'NFG_ACTIVE.json';assert not active.exists();active.write_text(json.dumps(dict(attempt=a,target=harness)))
def ssh(code,stdin=None,submitted=False):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,code],input=stdin,capture_output=True,text=True)
  with (E/'NFG_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=retry,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
  if r.returncode!=255 or submitted:return r
  if retry<10:time.sleep(60)
 raise SystemExit('transport exhausted')
vanished_retry=False
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
 if 'FileNotFoundError' in str(ad.get('error','')):
  err=str(ad['error'])
  own=[json.loads(p.read_text()).get('cgroup','') for p in E.glob('NFG_*/receipt.json')]
  assert '/sys/fs/cgroup/' in err and not any(c and c in err for c in own),'STOP infrastructure: vanished own/non-cgroup path'
  if vanished_retry:raise SystemExit('STOP infrastructure: repeated vanished-cgroup scan failure')
  vanished_retry=True;time.sleep(30);continue
 if (r.returncode==78 or ad.get('allowed') is False) and retry<10:print('reservation refused; wait three minutes',flush=True);time.sleep(180);continue
 raise SystemExit('STOP infrastructure admission')
verifier=harness.startswith(('verifier::','fast_pairing::'))
ni=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+'/NFG_src/crates/'+('aspis-r1-cost-probe' if verifier else 'aspis-core')+'/Cargo.toml','--target-dir',B+'/NFG_target','--features','private-leaf-salts,optimized-terminal,program-build' if verifier else 'r0','--lib','-j','1','-Z','unstable-options','-Z','function-contracts','-Z','stubbing','--harness-timeout','90s','--exact','--harness',target,'--output-format','terse']
env=dict(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG='0',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',RUSTFLAGS='-C link-arg=-Wl,--threads=1',TMPDIR=B+'/NFG_tmp')
if flag:
 assert len(flag)<=2 and len(set(flag))==len(flag)
 assert all(f in ['NFG_bad_neg','NFG_bad_zero','NFG_bad_reply','NFG_bad_argument','NFG_reject_lower','NFG_reject_upper']+['NFG_reject_k_'+str(k).zfill(2) for k in range(12)]+['NET_reserve_only','NET_one_push','NET_only_new','NET_only_frame','NET_bad_reply','NET_bad_argument','NET_bad_frame','NET_bad_order','NET_bad_option']+['NFG_wrong_field','NFG_wrong_badfield','NFG_wrong_empty','NFG_wrong_index','NFG_wrong_opening','NFG_wrong_inverse','NFG_wrong_zero','NFG_wrong_cell','NFG_wrong_window','NFG_wrong_getter','NFG_wrong_q','NFG_wrong_geometry','NFG_wrong_reduce','NFG_wrong_wrapper']+['NFG_wrong_'+p+'_'+o for p in ['m','c','q','e'] for o in ['add','sub','double']]+['NFG_wrong_limbs','NFG_wrong_canonical','NFG_wrong_embed'] for f in flag)
 assert len(set(flag)&{'NET_only_new','NET_only_frame','NET_reserve_only','NET_one_push'})<=1
 for f in flag:env['RUSTFLAGS']+=' --cfg '+f
sources=['NFG_TOOL_PINS.json','NFG_gate.py','NFG_graph.py','NFG_SOURCE_PINS.json','NFG_src/Cargo.lock','NFG_src/Cargo.toml','NFG_src/KMX_stubs.rs','NFG_src/KMX_native.rs','NFG_src/KMX_CopyMeaning.lean','NFG_src/crates/aspis-core/src/field.rs','NFG_src/crates/aspis-core/src/lib.rs','NFG_src/crates/aspis-core/src/field.rs']

if verifier:sources += ['NFG_src/crates/aspis-r1-cost-probe/src/'+p for p in ['verifier.rs','lib.rs','weights.rs','candidate.rs','fast_dots.rs']]
sources += ['NFG_src/'+p for p in json.loads((E/'NFG_SOURCE_PINS.json').read_text()) if '/NFG_' in p and 'NFG_src/'+p not in sources]
cfg=dict(attempt=a,kind='kani',target=target,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),source_tree_dirty=True,sources=sources,command=['python3','NFG_gate.py',a+'.json'],native_command=ni,timeout=180,env=env,deps_fingerprint=dict(source_pinset='NFG_SOURCE_PINS.json',frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'),expected_time='Optimized compilation then '+target+' native cut; field multiplication bodies never execute in the gate, only the documented Lean-discharged oracle specification',copy_patch_sha256=hashlib.sha256((E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch').read_bytes()).hexdigest(),feature_scope=('deployed verifier default/private-leaf-salts/optimized-terminal/program-build; statement r0/pool-v1-kernel and resolved optimized features recorded per crate' if verifier else 'core r0 helper, feature-independent frozen method bodies; cfg(kani) instrumentation only'),copy_dependency='KMX-approved copy implementation applied; scalar-only reducer has no copy dependence, record/array lanes require matched KMX positive/negative controls')
(E/(a+'.json')).write_text(json.dumps(cfg,indent=1)+'\n')
files={'NFG_TOOL_PINS.json':(E/'NFG_TOOL_PINS.json').read_text(),'NFG_gate.py':(E/'NFG_gate.py').read_text(),'NFG_graph.py':(E/'NFG_graph.py').read_text(),a+'.json':json.dumps(cfg)}
r=ssh('python3',f'''from pathlib import Path
import json
b=Path({B!r})
for n,s in json.loads({json.dumps(files)!r}).items():(b/n).write_text(s)
''');assert r.returncode==0,r.stderr
r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
names=[a+'/receipt.json',a+'/stdout.log',a+'/time.log',a+'-graph-check.json',a+'-graph.stderr',a+'-lock-check.json',a+'-source-check.json',a+'-tool-check.json',a+'/sources/NFG_gate.py',a+'/sources/NFG_graph.py']
r=ssh('python3',f'''from pathlib import Path
import json
b=Path({B!r});print(json.dumps({{n:(b/n).read_text() for n in {names!r} if (b/n).exists()}}))
''');assert r.returncode==0,r.stderr
out=json.loads(r.stdout)
for n,s in out.items():p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
assert a+'/receipt.json' in out,'submitted attempt unresolved; recover read-only, never resubmit'
rc=json.loads(out[a+'/receipt.json'])
with (E/'NFG_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(rc)+'\n')
subprocess.run([sys.executable,str(E/'NFG_recover_sources.py'),a],check=True)
active.unlink()
print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps']}),flush=True);print('\n'.join(line for line in out[a+'/stdout.log'].splitlines() if any(t in line for t in ['Checking harness','VERIFICATION','failed (','Failed Checks:','error:','Verification Time:'])),flush=True)
if rc['exit_status'] in [124,137] or 'timed out' in out[a+'/stdout.log'].lower():raise SystemExit('STOP timed-out shape; isolate and split, never rerun unchanged')
sys.exit(rc['exit_status'])
