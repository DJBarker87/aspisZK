"""Own serial transport wrapper; invokes byte-identical S2H/S2W backends.
Batches transfer/recovery to avoid repeated flaky connections. No backend edits.
"""
from pathlib import Path
import subprocess,sys,json,time,shlex,hashlib
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-native-prepare5-20261028';C='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025';X='/home/dombarker/project-offloads/codex-cx-assoc-a2-cache-20261027/XRw_objects'
a,module=sys.argv[1:]
core=module.startswith('r0_transcript::NCH_query::')
package='aspis-core' if core else 'aspis-r1-cost-probe'
rel='crates/'+package+'/src/'+('NCH_query_core.rs' if core else 'NCH_sampler.rs' if module.startswith('sampler::NCH_sampler::') else 'NCH_verifier.rs')
src='NCH_src/crates/aspis-r1-cost-probe/src/NCH_candidate.rs';local=Path('/private/tmp/NCH_candidate.rs');obj='/dev/null'

import os
if (E/'NCH_PAUSE').exists():raise SystemExit('paused before admission')
active=E/'NCH_ACTIVE.json'
try:
 fd=os.open(active,os.O_CREAT|os.O_EXCL|os.O_WRONLY,0o600)
except FileExistsError:
 raise SystemExit('STOP own attempt active; recover its terminal receipt before launching: '+active.read_text())
with os.fdopen(fd,'w') as f:json.dump(dict(attempt=a),f)
if (E/'NCH_BUDGET_STOP.json').exists() and json.loads((E/'NCH_BUDGET_STOP.json').read_text()).get('kani_exhausted',False):raise SystemExit('kani allocation exhausted: no kani launches')
assert len(list(E.glob('NCH_K[0-9][0-9][0-9].json')))<70
assert not (E/a/'receipt.json').exists()
def ssh(code,submitted=False,stdin=None):
 argv=['ssh','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2','-o','ControlMaster=no',H,code]
 for n in range(11):
  r=subprocess.run(argv,capture_output=True,text=True,input=stdin)
  with (E/'NCH_STEP_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,trial=n,exit=r.returncode,stdout=r.stdout,stderr=r.stderr,submitted=submitted,argv=argv))+'\n')
  if r.returncode!=255 or submitted:return r
  if n<10:print('prelaunch/read-only transport retry60s',flush=True);time.sleep(60)
 raise SystemExit('STOP transport exhausted')
for retry in range(11):
 script=f'''from pathlib import Path
import subprocess,sys
b=Path({B!r});b.mkdir(exist_ok=True)
p=b/{(a+'-barrier-'+str(retry)+'.log')!r}
with p.open('w') as f:
 r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/{(a+'-reservation.json')!r})],stdout=f,stderr=subprocess.STDOUT)
print(p.read_text(),end='');sys.exit(r.returncode)
'''
 r=ssh('python3 -c '+shlex.quote(script));(E/(a+f'-barrier-{retry}.log')).write_text(r.stdout+r.stderr)
 try:ad=next(json.loads(l) for l in r.stdout.splitlines() if l.startswith('{'))
 except (StopIteration,json.JSONDecodeError):
  if retry==0:time.sleep(30);continue
  raise SystemExit('STOP admission JSON missing '+r.stdout+r.stderr)
 (E/(a+'-reservation.json')).write_text(json.dumps(ad,indent=2)+'\n')
 if r.returncode==0 and ad.get('allowed') is True:break
 if (r.returncode==78 or ad.get('allowed') is False) and retry<10:print('admission refused; wait180s',flush=True);time.sleep(180);continue
 raise SystemExit('STOP admission error')
else:raise SystemExit('STOP admission exhausted')
(E/(a+'-harness.patch')).write_bytes((E/'NCH_harness.patch').read_bytes())
pinbytes=(E/'NCH_SOURCE.json').read_bytes();pinhash=hashlib.sha256(pinbytes).hexdigest();pinbase=E/('NCH_PINSET_'+pinhash[:20]+'.json')
if not pinbase.exists():pinbase.write_bytes(pinbytes)
assert pinbase.read_bytes()==pinbytes
(E/(a+'-source-pin.json')).write_text(json.dumps(dict(schema='NCH-source-pin-reference-v1',pinset=pinbase.name,sha256=pinhash,bytes=len(pinbytes),original_sha256=pinhash),indent=2)+'\n')
cfg=dict(attempt=a,kind='kani',module=module,sources=[src,'NCH_src/crates/aspis-r1-cost-probe/src/lib.rs','NCH_src/crates/aspis-r1-cost-probe/src/verifier.rs','NCH_src/crates/aspis-core/src/r0_transcript.rs','NCH_src/crates/aspis-r1-cost-probe/src/sampler.rs','NCH_src/Cargo.toml','NCH_src/Cargo.lock','NCH_src/KMX_stubs.rs','NCH_src/crates/aspis-r1-cost-probe/src/r1_wire.rs'],command=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+'/NCH_src/crates/'+package+'/Cargo.toml','--target-dir',B+'/NCH_target','--lib','-j','1','-Z','unstable-options','-Z','function-contracts','-Z','stubbing','--harness-timeout','90s','--exact','--harness',module,'--output-format','terse'],timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,env={'PATH':'/home/dombarker/.cargo/bin:/usr/bin:/bin','CARGO_BUILD_JOBS':'1','CARGO_NET_OFFLINE':'true','CARGO_PROFILE_DEV_OPT_LEVEL':'3','CARGO_PROFILE_DEV_DEBUG':'0','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS':'true','RUSTFLAGS':'-C link-arg=-Wl,--threads=1','TMPDIR':B+'/NCH_tmp'},deps_fingerprint={'scope':'frozen native source selected by NCH_SOURCE.json; graph audit before every run; arbitrary callee return overapproximations'},expected_time='optimized Kani compilation then native call routing; no arithmetic elimination',reservation_retries=retry)
if os.environ.get('NCH_KANI_PATTERN')=='1':
 cfg['command'].remove('--exact')
 cfg['harness_selection']='prefix substring, four targets serially at -j1; one cargo-kani invocation'
 cfg['expected_harnesses']=['NCH_row_borrow_domain','NCH_row_borrow_wrong','NCH_cell_borrow_domain','NCH_cell_borrow_wrong']
if os.environ.get('NCH_KANI_TRACE')=='1':
 cfg['command'][cfg['command'].index('terse')]='regular'
 cfg['command']+=['--cbmc-args','--trace']
cfg['copy_patch_sha256']='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
cfg['native_command']=cfg['command'];cfg['command']=['python3','NCH_gate.py',a+'.json']
(E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
q=E/a/'sources'/src;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(local.read_bytes())
payload=dict(cfg=cfg,source=local.read_text(),src=src,obj=obj,launchers=json.loads((E/'NCH_LAUNCHER_INPUTS.json').read_text()),gate=(E/'NCH_gate.py').read_text(),pins=json.loads((E/'NCH_SOURCE.json').read_text())['source_sha256'])
# Data serialization is shell-quoted; input source is never shell code.
setup=f'''from pathlib import Path
import json,hashlib
b=Path({B!r});x=json.loads({json.dumps(json.dumps(payload))})
for n in ['S2W_lean_host.py','S2W_run_host.py','lakefile.toml','lean-toolchain','lake-manifest.json']:
 p=b/n;s=x['launchers'][n]
 if p.exists():assert p.read_text()==s,(n,'unchanged backend mismatch')
 else:p.write_text(s)
(b/'NCH_tmp').mkdir(exist_ok=True)
(b/'NCH_gate.py').write_text(x['gate'])
(b/'NCH_SOURCE_PINS.json').write_text(json.dumps(x['pins']))
(b/x['src']).write_text(x['source']);(b/{(a+'.json')!r}).write_text(json.dumps(x['cfg'],indent=2)+'\\n')
c=Path({C!r})/'objects';paths=[c/'Aeneas.olean']+list((c/'Aeneas').rglob('*.olean'))
pins={{str(p):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size) for p in paths}}
p=b/'NCH_LIBRARY_PIN.json'
if p.exists(): assert json.loads(p.read_text())==pins,'library pin changed'
else:p.write_text(json.dumps(pins,indent=2)+'\\n')
'''
# Submission is never retried, including transport failures; recover read-only.
prepared=ssh('python3',stdin=setup);assert prepared.returncode==0,prepared.stdout+prepared.stderr
cmd='cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+shlex.quote(a+'.json')
r=ssh(cmd,submitted=True);(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
post=ssh('sha256sum '+shlex.quote(B+'/NCH_src/Cargo.lock'));(E/(a+'-lock-after.log')).write_text(post.stdout+post.stderr)
assert post.returncode==0 and post.stdout.split()[0]=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef','STOP lock drift'
recover=f'''from pathlib import Path
import json
b=Path({B!r});names=[{(a+'/receipt.json')!r},{(a+'/stdout.log')!r},{(a+'/time.log')!r},'NCH_LIBRARY_PIN.json',{(a+'-graph-check.json')!r},{(a+'-source-check.json')!r},{(a+'-graph.stderr')!r},{(a+'-lock-check.json')!r}]
print(json.dumps({{n:(b/n).read_text() for n in names if (b/n).is_file()}}))
'''
r=ssh('python3 -c '+shlex.quote(recover));assert r.returncode==0,r.stderr
out=json.loads(r.stdout)
for n,s in out.items():p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
if a+'/receipt.json' not in out:raise SystemExit('STOP no prover receipt; inspect setup/launcher, do not resubmit blindly')
rc=json.loads(out[a+'/receipt.json']);print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}));print(out[a+'/stdout.log'][-650:])

with (E/'NCH_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(rc)+'\n')
assert json.loads(active.read_text())["attempt"]==a
active.unlink()
