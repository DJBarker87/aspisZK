"""Invoke unchanged S2H admission and S2W runners, serially, for this job."""
from pathlib import Path
import subprocess,json,sys,time,hashlib
E=Path(__file__).resolve().parent
H='dombarker@100.108.41.90'; B='/home/dombarker/project-offloads/codex-cx-libmodel2-cache-20261027'; C='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025'; K='/home/dombarker/project-offloads/codex-cx-assoc-a4-cache-20261027'
a,kind,source=sys.argv[1:]; src=Path(source); module=src.stem
assert kind in ['lean','rust']
assert int(a.split('_')[-1][1:]) <= (80 if kind=='lean' else 10)
assert not (E/a/'receipt.json').exists()
def remote(cmd,submitted=False):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ConnectTimeout=20',H,cmd],capture_output=True,text=True)
  if r.returncode!=255:return r
  with (E/'KSC2_transport.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=retry,submitted=submitted,stderr=r.stderr))+'\n')
  if submitted:raise SystemExit('Submitted transport lost; recover read-only, do not resubmit')
  if retry==10:raise SystemExit('STOP persistent prelaunch transport failure')
  time.sleep(60)
def get(n):
 p=E/n;p.parent.mkdir(parents=True,exist_ok=True)
 r=remote('cat '+B+'/'+n);assert r.returncode==0,r.stderr;p.write_text(r.stdout)
# Create private cache and reuse unchanged infrastructure; no shared object modifications.
r=remote('mkdir -p '+B+'/KSC2_generated '+B+'/KSC2_objects; cp -n '+C+'/S2W_lean_host.py '+C+'/S2W_run_host.py '+B+'/');assert r.returncode==0,r.stderr
for retry in range(11):
 log=a+f'-barrier-{retry}.log';r=remote(f'python3 /home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py {B}/{a}-reservation.json > {B}/{log} 2>&1');get(log)
 exists=remote('test -f '+B+'/'+a+'-reservation.json').returncode==0
 if not exists and retry==0:time.sleep(30);continue
 if exists:
  get(a+'-reservation.json');ad=json.loads((E/(a+'-reservation.json')).read_text())
  if r.returncode==0 and ad['allowed']:break
  if (r.returncode==78 or not ad['allowed']) and retry<10:print('reservation refused, waiting',flush=True);time.sleep(180);continue
 if 'FileNotFoundError' in (E/log).read_text() and retry==0:time.sleep(30);continue
 raise SystemExit('STOP admission '+r.stderr)
else:raise SystemExit('STOP admission exhausted')
(E/(a+'-admission.json')).write_text(json.dumps(dict(exit_status=r.returncode,allowed=ad['allowed'],retry=retry))+'\n')
pins=json.load(open(E.parent/'kit-audit1-20261027/KSA_L021.json'))['deps_fingerprint']['aeneas_library_objects']
# Verify the entire inherited selection against current objects before submission.
check=remote("python3 - <<'PIN'\nimport hashlib,json\npins="+repr(pins)+"\nfor p,h in pins.items():\n assert hashlib.sha256(open(p,'rb').read()).hexdigest()==h,p\nprint(json.dumps(pins))\nPIN");assert check.returncode==0,check.stderr
cfg=dict(attempt=a,kind=kind,module=module,sources=[],timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,env={},deps_fingerprint={'aeneas_library_objects':pins},reservation_retries=retry)
if kind=='lean':
 rel='KSC2_generated/'+src.name;cfg['sources']=[rel];cfg['command']=['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','KSC2_generated','-o','KSC2_objects/'+module+'.olean',rel];cfg['env']['LEAN_PATH']=':'.join([B+'/KSC2_objects',K+'/KSA_objects',K+'/XSd_objects',K+'/XRz_objects',K+'/XRx_objects',K+'/XRw_objects',C,C+'/objects']);cfg['expected_time']='single focused theorem elaboration; no heavy numeral reduction'
else:
 rel=src.name;cfg['sources']=[rel,'KSC2_native_test.rs'];cfg['command']=['python3',rel];cfg['env']={'CARGO_NET_OFFLINE':'true'};cfg['expected_time']='std-only optimized rustc test compilation followed by tiny branch differentials; cargo validates frozen offline graph first';cfg['timeout']=180
(E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
for local,dest in [(src,rel),(E/(a+'.json'),a+'.json')]+([(E/'KSC2_native_test.rs','KSC2_native_test.rs')] if kind=='rust' else []):
 for retry in range(11):
  r=subprocess.run(['scp','-q','-o','ConnectTimeout=20',str(local),H+':'+B+'/'+dest],capture_output=True,text=True)
  if r.returncode!=255:break
  with (E/'KSC2_transport.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,operation='scp',retry=retry,stderr=r.stderr))+'\n')
  if retry==10:raise SystemExit('STOP scp retries')
  time.sleep(60)
 assert r.returncode==0,r.stderr
runner='S2W_lean_host.py' if kind=='lean' else 'S2W_run_host.py'
r=remote(f'cd {B} && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 {runner} {a}.json',submitted=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
for n in ['receipt.json','stdout.log','time.log']:get(a+'/'+n)
rc=json.loads((E/a/'receipt.json').read_text());print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}));print((E/a/'stdout.log').read_text()[-7000:])
q=E/a/'sources'/rel;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(src.read_bytes())
