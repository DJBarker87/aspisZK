"""Serial invocation of the unchanged S2H admission and S2W runners."""
from pathlib import Path
import subprocess,sys,json,time
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-leaf-p6-15-20261027';C='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025'
a,local,module=sys.argv[1:];local=Path(local);src='LPq_generated/'+module.replace('.','/')+'.lean';obj='LPq_objects/'+module.replace('.','/')+'.olean'
assert len(list(E.glob('LPq_L*/receipt.json'))) < 80, 'STOP proof budget exhausted'
def transport(argv, submitted=False):
 for trial in range(11):
  r=subprocess.run(argv,capture_output=True,text=True)
  row=dict(argv=argv,trial=trial,exit=r.returncode,stdout=r.stdout,stderr=r.stderr,submitted=submitted)
  with (E/'LPq_STEP_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(row)+'\n')
  if r.returncode!=255:return r
  if submitted:return r # recover output read-only; NEVER resubmit
  if trial<10:print('transport retry60s',flush=True);time.sleep(60)
 raise SystemExit('STOP persistent transport failure')
def ssh(s, submitted=False):return transport(['ssh','-o','ConnectTimeout=15',H,s],submitted)
def get(n):
 (E/n).parent.mkdir(parents=True,exist_ok=True)
 r=transport(['scp','-q','-o','ConnectTimeout=15',H+':'+B+'/'+n,str(E/n)]); assert r.returncode==0,r.stderr
r=ssh(f'mkdir -p {B}'); assert r.returncode==0,r.stderr
for retry in range(11):
 log=a+f'-barrier-{retry}.log';r=ssh(f'python3 /home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py {B}/{a}-reservation.json > {B}/{log} 2>&1');get(log)
 exists=ssh(f'test -f {B}/{a}-reservation.json').returncode==0
 if not exists and retry==0:time.sleep(30);continue
 if exists:
  get(a+'-reservation.json');ad=json.loads((E/(a+'-reservation.json')).read_text())
  if r.returncode==0 and ad['allowed']:break
  if (r.returncode==78 or not ad['allowed']) and retry<10:print('reservation wait',flush=True);time.sleep(180);continue
 if 'FileNotFoundError' in (E/log).read_text() and retry==0:time.sleep(30);continue
 raise SystemExit('STOP admission '+r.stdout+r.stderr)
else:raise SystemExit('STOP admission retries')
cfg=dict(attempt=a,kind='lean',module=module,sources=[src],command=['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','LPq_generated','-o',obj,src],timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,env={'LEAN_PATH':B+'/LPq_objects:/home/dombarker/project-offloads/codex-cx-assoc-a2-cache-20261027/XRw_objects:'+C+':'+C+'/objects:/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean'},deps_fingerprint={'scope':'Private LPq modules and unchanged dependencies on coherent SInt2 objects'},expected_time='single module elaboration, no concrete arithmetic normalization',reservation_retries=retry)
(E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
r=ssh(f'mkdir -p {B}/{str(Path(src).parent)} {B}/{str(Path(obj).parent)} && cp /home/dombarker/project-offloads/codex-cx-leaf-p6-11-20261027/S2W_lean_host.py {B}/S2W_lean_host.py');assert r.returncode==0,r.stderr
r=transport(['scp','-q','-o','ConnectTimeout=15',str(local),H+':'+B+'/'+src]); assert r.returncode==0,r.stderr
r=transport(['scp','-q','-o','ConnectTimeout=15',str(E/(a+'.json')),H+':'+B+'/'+a+'.json']); assert r.returncode==0,r.stderr
r=ssh(f'cd {B} && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_lean_host.py {a}.json', submitted=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
for n in ['receipt.json','stdout.log','time.log']:get(a+'/'+n)
rc=json.loads((E/a/'receipt.json').read_text());print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}));print((E/a/'stdout.log').read_text()[-14000:])
# Preserve the exact compiler input snapshot locally with the receipt.
q=E/a/'sources'/src;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(local.read_bytes())
