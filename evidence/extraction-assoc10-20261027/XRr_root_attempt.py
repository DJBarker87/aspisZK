"""Serial invocation of the unchanged S2H admission and S2W runners."""
from pathlib import Path
import subprocess,sys,json,time
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-extraction-assoc10-20261027';C='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025'
a,local,module=sys.argv[1:];local=Path(local);src='XRr_generated/'+module.replace('.','/')+'.lean';obj='XRr_objects/'+module.replace('.','/')+'.olean'
def ssh(s):return subprocess.run(['ssh',H,s],capture_output=True,text=True)
def get(n):
 (E/n).parent.mkdir(parents=True,exist_ok=True)
 subprocess.run(['scp','-q',H+':'+B+'/'+n,str(E/n)],check=True)
for retry in range(11):
 log=a+f'-barrier-{retry}.log';r=ssh(f'python3 /home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py {B}/{a}-reservation.json > {B}/{log} 2>&1');get(log)
 exists=ssh(f'test -f {B}/{a}-reservation.json').returncode==0
 if not exists and retry==0:time.sleep(30);continue
 if exists:
  get(a+'-reservation.json');ad=json.loads((E/(a+'-reservation.json')).read_text())
  if r.returncode==0 and ad['allowed']:break
  if (r.returncode==78 or 'quiet window' in ad.get('reason','')) and retry<10:print('reservation wait',flush=True);time.sleep(180);continue
 if 'FileNotFoundError' in (E/log).read_text() and retry==0:time.sleep(30);continue
 raise SystemExit('STOP admission '+r.stdout+r.stderr)
else:raise SystemExit('STOP admission retries')
cfg=dict(attempt=a,kind='lean',module=module,sources=[src],command=['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','XRr_generated','-o',obj,src],timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,env={'LEAN_PATH':'/home/dombarker/project-offloads/codex-cx-replay-dry-20261026/RPx_overlay:/home/dombarker/project-offloads/codex-cx-replay-dry-20261026/RPv_overlay:/home/dombarker/project-offloads/codex-cx-replay-dry-20261026/RPu_overlay:/home/dombarker/project-offloads/codex-cx-replay-dry-20261026/RPt_overlay:/home/dombarker/project-offloads/codex-cx-replay-dry-20261026/RPz8_overlay:/home/dombarker/project-offloads/codex-cx-replay-dry-20261026/RPz7_overlay:/home/dombarker/project-offloads/codex-cx-replay-dry-20261026/RPz4_trusted:/home/dombarker/project-offloads/codex-cx-replay-dry-20261026/RPz_trusted'},deps_fingerprint={'scope':'isolated release external definitions and emitted release; coherent objects'},expected_time='single module elaboration, no concrete arithmetic normalization',reservation_retries=retry)
(E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
r=ssh(f'mkdir -p {B}/{str(Path(src).parent)} {B}/{str(Path(obj).parent)}');assert r.returncode==0,r.stderr
subprocess.run(['scp','-q',str(local),H+':'+B+'/'+src],check=True)
subprocess.run(['scp','-q',str(E/(a+'.json')),H+':'+B+'/'+a+'.json'],check=True)
r=ssh(f'cd {B} && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_lean_host.py {a}.json')
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
for n in ['receipt.json','stdout.log','time.log']:get(a+'/'+n)
rc=json.loads((E/a/'receipt.json').read_text());print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}));print((E/a/'stdout.log').read_text()[-14000:])
# Preserve the exact compiler input snapshot locally with the receipt.
q=E/a/'sources'/src;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(local.read_bytes())
