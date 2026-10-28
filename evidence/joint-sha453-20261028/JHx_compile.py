"""Task orchestration only: use unchanged lead-owned admission and launchers."""
from pathlib import Path
import json, subprocess, sys, time, shlex
E=Path(__file__).resolve().parent; R=E.parents[1]
B='/home/dombarker/project-offloads/codex-cx-sha453-cache-20261028'
H='dombarker@100.108.41.90'
OPTIONS=['-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2']
def event(**row):
 with (E/'JHx_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(utc=time.time(),**row))+'\n')
def transport(args,submitted=False):
 for retry in range(10):
  r=subprocess.run(args,text=True,capture_output=True)
  if r.returncode!=255:return r
  event(command=args,exit_status=255,retry=retry,submitted=submitted)
  if submitted:return r
  if retry<9:time.sleep(60)
 raise SystemExit('Persistent transport failure')
def ssh(command,submitted=False):return transport(['ssh',*OPTIONS,H,command],submitted)
mode,attempt,module=sys.argv[1:]
assert mode in ('preflight','large') and attempt.startswith('JHx_') and module.startswith('JHx_')
assert not (E/attempt).exists()
cfg=json.loads((R/'evidence/joint-agg2-20261028/JHw_C.json').read_text())
cfg={k:cfg[k] for k in ['kind','env','deps_fingerprint','command']}
cfg.update(attempt=attempt,sources=[module+'.lean'],source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=subprocess.check_output(['git','status','--porcelain'],text=True).strip()!='',timeout=540,expected_time='Bounded single-round SHA256 certificates and symbolic block chaining; assembly imports and named applications')
cfg['command']=[*cfg['command'][:3],'-j1','-M15000' if mode=='large' else '-M7000','-DElab.async=false','-o',module+'.olean',module+'.lean']
cfg['env']['LEAN_PATH']=B+':'+cfg['env']['LEAN_PATH']
cfg['deps_fingerprint']={'scope':'JHq owner-approved TX1 aggregation; inherited joint-fixture35 lane'}
(E/(attempt+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
script=B+'/reservation_agg16.py' if mode=='large' else '/home/dombarker/project-offloads/codex-cx-s2c-20261023/reservation.py'
admissions=[]
for retry in range(11):
 prefix=B+'/'+attempt+'-reservation-'+str(retry)
 command=f'python3 {script} {prefix}.json > {prefix}.log 2>&1'
 result=ssh(command)
 receipt=ssh(f'cat {prefix}.log; test ! -f {prefix}.json || cat {prefix}.json')
 (E/(attempt+'-barrier-'+str(retry)+'.log')).write_text(receipt.stdout+receipt.stderr)
 raw=ssh(f'cat {prefix}.json')
 try:admission=json.loads(raw.stdout)
 except ValueError:admission={}
 admissions.append(dict(retry=retry,command=command,exit_status=result.returncode,receipt=admission))
 (E/(attempt+'-admission.json')).write_text(json.dumps(admissions,indent=2)+'\n')
 if result.returncode==0 and admission.get('allowed') is True:break
 if result.returncode==78 or admission.get('allowed') is False:
  print('Admission refused; waiting 180 seconds',flush=True);time.sleep(180);continue
 if not admission and retry==0:
  print('Missing receipt; transient retry after 30 seconds',flush=True);time.sleep(30);continue
 raise SystemExit('Admission failure: '+receipt.stdout+receipt.stderr)
else:raise SystemExit('Admission retry budget exhausted')
for source,destination in [(R/'lean'/(module+'.lean'),B+'/'+module+'.lean'),(E/(attempt+'.json'),B+'/'+attempt+'.json')]:
 r=transport(['scp',*OPTIONS,'-q',str(source),H+':'+destination]);assert r.returncode==0,r.stderr
caps='-p MemoryHigh=14G -p MemoryMax=16G' if mode=='large' else '-p MemoryHigh=6G -p MemoryMax=8G'
launcher='S2W_lean_host_agg16.py' if mode=='large' else 'S2W_lean_host.py'
command=f'cd {B} && systemd-run --user --scope {caps} -p MemorySwapMax=0 -p TasksMax=64 python3 {launcher} {attempt}.json'
(E/(attempt+'-command.txt')).write_text(command+'\n')
r=ssh(command,submitted=True)
(E/(attempt+'-launch.log')).write_text(r.stdout+r.stderr)
print(r.stdout+r.stderr,flush=True)
if r.returncode==255:
 for retry in range(10):
  time.sleep(60)
  recovered=ssh(f'test -f {B}/{attempt}/receipt.json')
  if recovered.returncode==0:break
 else:raise SystemExit('Submitted attempt unresolved; no resubmission')
r=transport(['scp',*OPTIONS,'-qr',H+':'+B+'/'+attempt,str(E)])
assert r.returncode==0,r.stderr
receipt=json.loads((E/attempt/'receipt.json').read_text())
print(json.dumps({k:receipt[k] for k in ['exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']},indent=2),flush=True)
with (E/'JHx_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=attempt,mode=mode,**receipt))+'\n')
sys.exit(receipt['exit_status'])
