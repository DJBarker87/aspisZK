"""JHm30 task orchestration; invokes unchanged host admission and Lean launcher."""
from pathlib import Path
import json,subprocess,sys,time,shlex
P=Path(__file__).resolve().parent; R=P.parents[1]
B='/home/dombarker/project-offloads/codex-cx-fixture-cache-20261027'; HOST='dombarker@100.108.41.90'
def ssh(cmd,**kw):
 for tr in range(10):
  result=subprocess.run(['ssh','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2',HOST,cmd],**kw)
  if result.returncode!=255 or 'systemd-run' in cmd:return result
  with (P/'JHm_TRANSPORT.jsonl').open('a') as log:
   log.write(json.dumps(dict(step=cmd,retry=tr,exit_status=255,wait_seconds=60 if tr<9 else 0))+'\n')
  if tr<9:time.sleep(60)
 raise SystemExit(255)
n=int(sys.argv[1]); mod=sys.argv[2]; assert 1<=n<=100
if False:
 print('Local proof-stage boundary before tree1C: split continuation before admission; no Lean launched.');sys.exit(80)
if n==70 and mod!='JHm_Review70':
 print('Attempt70 is reserved for the required current-root/obstruction audit; no Lean launched.');sys.exit(70)
relative_source=mod.replace('.','/')+'.lean'
source_file=R/'lean'/relative_source
assert mod.startswith('JHm_')
a=f'JHm34_{n:03}'; assert not (P/a).exists()
cfg=json.loads((R/'evidence/joint-fixture12-20261026/JFu12_100/receipt.json').read_text())
cfg.update(attempt=a,sources=[relative_source],source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,expected_time='Focused JGr symbolic proof; exact arithmetic scope recorded below' )
hash_plan=json.loads((P/'JHm_HASH_PLAN.json').read_text()) if (P/'JHm_HASH_PLAN.json').exists() else []
row=next((r for r in hash_plan if r['module']==mod),None)
cfg['expected_time']=(f"Lean checks {row['blocks']} SHA compression blocks using named primitive round/word equations; no full hash normalization" if row else 'Symbolic source/model composition on pinned cached objects; no full concrete recurrence normalization')
cfg['deps_fingerprint']['scope']='JGr retained real-byte fixture continuation on coherent SInt2 objects; d18-v5 before aspis-joint'
cfg['env']['LEAN_PATH'] = B+':'+cfg['env']['LEAN_PATH']
cfg['env']['LEAN_PATH'] += ':/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/JFp_Cache:/home/dombarker/project-offloads/d18-circle-model-repin-v5-20261019/attempt/objects'
# Select the existing pinned circle namespace before the retired aggregate cache.
circle_cache='/home/dombarker/project-offloads/d18-circle-model-repin-v5-20261019/attempt/objects'
search_paths=[p for p in cfg['env']['LEAN_PATH'].split(':') if p!=circle_cache]
search_paths.insert(search_paths.index('/home/dombarker/project-offloads/codex-cx-parse-sem-20261025')+1,circle_cache)
cfg['env']['LEAN_PATH']=':'.join(search_paths)
if mod=='JHm_HeadlineAudit':
 cfg['env']=json.loads((R/'evidence/joint-fixture28-20261027/JHa_JGz_TX2_097.json').read_text())['env']
cfg['command'][-3:]=['-o',mod.replace('.','/')+'.olean',relative_source]
if mod=='JHm_HeadlineAudit':
 names=list(json.loads((P/'JHm_AENEAS_OBJECT_PINS.json').read_text())['objects'])
 pin_code='from pathlib import Path\nimport hashlib,json\npaths='+repr(cfg['env']['LEAN_PATH'].split(':'))+'\nnames='+repr(names)+'\nobjects={}\nfor name in names:\n p=next((Path(root)/name for root in paths if (Path(root)/name).is_file()),None)\n assert p is not None,name\n objects[name]=dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)\nprint(json.dumps(dict(selection="first match in JHm headline audit LEAN_PATH",objects=objects),indent=2))'
 pins=ssh('python3 -c '+shlex.quote(pin_code),capture_output=True,text=True)
 assert pins.returncode==0,pins.stderr
 json.loads(pins.stdout)
 (P/'JHm_HEADLINE_AENEAS_OBJECT_PINS.json').write_text(pins.stdout)
(P/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
retries=[]
admissions=[]
for retry in range(11):
 cmd=f'python3 /home/dombarker/project-offloads/codex-cx-s2c-20261023/reservation.py {B}/{a}-reservation.json > {B}/{a}-barrier.log 2>&1'
 r=ssh(cmd)
 # Admission diagnostics are already durable on the host, before any scp.
 sshout=ssh(f'cat {B}/{a}-barrier.log',capture_output=True,text=True)
 (P/(a+'-barrier.log')).write_text(sshout.stdout+sshout.stderr)
 exists=ssh(f'test -f {B}/{a}-reservation.json').returncode==0
 admission=json.loads(ssh(f'cat {B}/{a}-reservation.json',capture_output=True,text=True).stdout) if exists else {}
 admissions.append(dict(retry=retry,exit_status=r.returncode,receipt=admission))
 (P/(a+'-admission.json')).write_text(json.dumps(admissions,indent=2)+'\n')
 if r.returncode==0 and admission.get('allowed') is True:break
 if (r.returncode==78 or admission.get('allowed') is False) and retry<10:
  retries.append(dict(wait_seconds=180,reason='reservation contention')); print('Reservation contention; waiting 180s',flush=True);time.sleep(180);continue
 if (not exists or 'FileNotFoundError' in sshout.stdout) and retry==0:
  retries.append(dict(wait_seconds=30,reason='transient missing receipt/vanished cgroup'));time.sleep(30);continue
 print(sshout.stdout+sshout.stderr);sys.exit(r.returncode or 1)
subprocess.run(['scp','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2','-q',str(source_file),HOST+':'+B+'/'+relative_source],check=True)
subprocess.run(['scp','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2','-q',str(P/(a+'.json')),HOST+':'+B+'/'],check=True)
r=ssh(f'cd {B} && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_lean_host.py {a}.json',capture_output=True,text=True)
(P/(a+'-launch.log')).write_text(r.stdout+r.stderr); print((r.stdout+r.stderr)[-2200:])
subprocess.run(['scp','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2','-qr',HOST+':'+B+'/'+a,str(P)],check=True)
subprocess.run(['scp','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2','-q',HOST+':'+B+'/'+a+'-reservation.json',str(P)],check=True)
(P/(a+'-retries.json')).write_text(json.dumps(retries,indent=2)+'\n')
sys.exit(r.returncode)
