"""JHj_TX2 task orchestration; invokes unchanged host admission and Lean launcher."""
from pathlib import Path
import json,subprocess,sys,time,shlex
P=Path(__file__).resolve().parent; R=P.parents[1]
B='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025'; HOST='dombarker@100.108.41.90'
def ssh(cmd,**kw):
 for retry in range(11):
  result=subprocess.run(['ssh','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2',HOST,cmd],**kw)
  if result.returncode!=255 or 'systemd-run' in cmd or retry==10:return result
  with (P/'JHj_TRANSPORT.jsonl').open('a') as f:
   f.write(json.dumps(dict(step=cmd,exit=255,retry=retry+1,wait_seconds=60,time=time.time()))+'\n')
  print('Transient SSH failure before submission; retry after 60s',flush=True)
  time.sleep(60)

def copy(args):
 for retry in range(11):
  result=subprocess.run(['scp','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2',*args])
  if result.returncode!=255 or retry==10:
   result.check_returncode();return
  with (P/'JHj_TRANSPORT.jsonl').open('a') as f:
   f.write(json.dumps(dict(step='scp',args=args,exit=255,retry=retry+1,wait_seconds=60,time=time.time()))+'\n')
  print('Transient scp failure; retry after60s',flush=True);time.sleep(60)
n=int(sys.argv[1]); mod=sys.argv[2]; assert 1<=n<=100 and (mod.startswith('JHj_'))
a=f'JHj_TX2_{n:03}'; assert not (P/a).exists()
cfg=json.loads((R/'evidence/recount8-20261026/Rc8_002/receipt.json').read_text())
cfg.update(attempt=a,sources=[mod+'.lean'],source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,expected_time='Focused TX2 folded-root, query, finish and accepted-wrapper composition on retained bytes')
cfg['deps_fingerprint']['scope']='Pinned coherent SInt2 closure; JHj_TX2 per-stage source snapshots and inherited unchanged object pins'
if mod.startswith('JHj_SHA'):
 cfg['expected_time']='Kernel checking at most16 SHA256 compression blocks, each64 bounded named transition cuts; no full hash reduction'
elif any(t in mod for t in ['Native','Digest','SHA','Realizes','HashTools']):
 cfg['expected_time']='Focused symbolic byte/chunk/padding/hash join using checked SHA transition certificates; no whole-buffer normalization'
pin='/home/dombarker/project-offloads/d18-circle-model-repin-v5-20261019/attempt/objects'
cfg['env']['LEAN_PATH'] = pin+':'+':'.join(x for x in cfg['env']['LEAN_PATH'].split(':') if x!=pin)
cfg['command'][-3:]=['-o',mod+'.olean',mod+'.lean']
if mod=='JHj_TopAudit':
 # Root-only audit in the adopted root's exact retained cohort, not a mixed import union.
 ref=json.loads((R/'evidence/replay-deployed2-20261027/RPx_0037/receipt.json').read_text())
 cfg['env']=ref['env']
 cfg['deps_fingerprint']['scope']='Adopted RPx root-only audit in unchanged retained RPx pinned cohort'
 cfg['expected_time']='One adopted headline axioms audit only; no package or manifest replay'
(P/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
retries=[]
for retry in range(11):
 cmd=f'python3 /home/dombarker/project-offloads/codex-cx-s2c-20261023/reservation.py {B}/{a}-reservation.json > {B}/{a}-barrier.log 2>&1'
 r=ssh(cmd)
 # Admission diagnostics are already durable on the host, before any scp.
 sshout=ssh(f'cat {B}/{a}-barrier.log',capture_output=True,text=True)
 (P/(a+'-barrier.log')).write_text(sshout.stdout+sshout.stderr)
 exists=ssh(f'test -f {B}/{a}-reservation.json').returncode==0
 reservation = ssh(f'cat {B}/{a}-reservation.json',capture_output=True,text=True) if exists else None
 admission = json.loads(reservation.stdout) if reservation and reservation.returncode == 0 else None
 if admission is not None:
  (P/(a+'-reservation.json')).write_text(json.dumps(admission,indent=2)+'\n')
 if r.returncode==0 and admission is not None and admission.get('allowed') is True:break
 if (r.returncode==78 or (admission is not None and admission.get('allowed') is False)) and retry<10:
  retries.append(dict(wait_seconds=180,reason='reservation contention')); print('Reservation contention; waiting 180s',flush=True);time.sleep(180);continue
 if (not exists or 'FileNotFoundError' in sshout.stdout) and retry==0:
  retries.append(dict(wait_seconds=30,reason='transient missing receipt/vanished cgroup'));time.sleep(30);continue
 print(sshout.stdout+sshout.stderr);sys.exit(r.returncode or 1)
src=R/'lean'/(mod+'.lean')
if not src.exists():src=R/'docs/research/100bit-spend-path-20261013/lean'/(mod+'.lean')
copy(['-q',str(src),str(P/(a+'.json')),HOST+':'+B+'/'])
r=ssh(f'cd {B} && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_lean_host.py {a}.json',capture_output=True,text=True)
(P/(a+'-launch.log')).write_text(r.stdout+r.stderr); print(r.stdout+r.stderr)
copy(['-qr',HOST+':'+B+'/'+a,str(P)])
copy(['-q',HOST+':'+B+'/'+a+'-reservation.json',str(P)])
(P/(a+'-retries.json')).write_text(json.dumps(retries,indent=2)+'\n')
sys.exit(r.returncode)
