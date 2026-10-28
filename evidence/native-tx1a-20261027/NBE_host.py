"""Own transport/validation wrapper around unchanged S2H/S2W infrastructure."""
import pathlib,subprocess,json,shlex,time,sys,hashlib
E=pathlib.Path(__file__).resolve().parent
H='dombarker@100.108.41.90'
B='/home/dombarker/project-offloads/codex-cx-native-tx1a-20261027'
C='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025'
CACHE='/home/dombarker/project-offloads/codex-cx-leaf-cache-20261027'
def ssh(code,submitted=False):
 for trial in range(10):
  r=subprocess.run(['ssh','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2',H,code],text=True,capture_output=True)
  with (E/'NBE_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(trial=trial,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
  if r.returncode!=255 or submitted:return r
  if trial<9:time.sleep(60)
 raise SystemExit('STOP transport exhausted')
def remote_py(code,submitted=False):return ssh('python3 -c '+shlex.quote(code),submitted)
def admit(a):
 for retry in range(11):
  r=remote_py(f'''from pathlib import Path
import subprocess,sys
b=Path({B!r});b.mkdir(exist_ok=True)
p=b/{(a+'-barrier-'+str(retry)+'.log')!r}
with p.open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/{(a+'-reservation.json')!r})],stdout=f,stderr=subprocess.STDOUT)
print(p.read_text(),end='');sys.exit(r.returncode)
''')
  (E/(a+f'-barrier-{retry}.log')).write_text(r.stdout+r.stderr)
  ad=next((json.loads(l) for l in r.stdout.splitlines() if l.startswith('{')),None)
  if ad is None:
   if retry==0:time.sleep(30);continue
   raise SystemExit('STOP missing admission JSON')
  (E/(a+'-reservation.json')).write_text(json.dumps(ad,indent=2)+'\n')
  if r.returncode==0 and ad.get('allowed') is True:return retry
  if (r.returncode==78 or ad.get('allowed') is False) and retry<10:print('wait180s admission',flush=True);time.sleep(180);continue
  raise SystemExit('STOP admission failure')
 raise SystemExit('STOP admission exhausted')
def recover(a):
 r=remote_py(f'''from pathlib import Path
import json
b=Path({B!r});names=[{(a+'/receipt.json')!r},{(a+'/stdout.log')!r},{(a+'/time.log')!r}]
print(json.dumps({{n:(b/n).read_text() for n in names if (b/n).is_file()}}))''')
 assert r.returncode==0,r.stderr
 for n,s in json.loads(r.stdout).items():p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
 if not (E/a/'receipt.json').exists():raise SystemExit('STOP unresolved receipt; do not resubmit')
 rc=json.loads((E/a/'receipt.json').read_text());print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}));print('\n'.join(l for l in (E/a/'stdout.log').read_text().splitlines() if any(w in l for w in ['error:', 'VERIFICATION', 'failed (', 'Checking harness', 'lock_before', 'Traceback', 'AssertionError', 'TIMEOUT'])))
 return rc
if __name__=='__main__':
 a=sys.argv[1]; assert not (E/a/'receipt.json').exists()
 if json.loads((E/(a+'.json')).read_text()).get('deferred'):
  print('DEFERRED before admission: '+a);raise SystemExit(0)
 retry=admit(a)
 cfg=json.loads((E/(a+'.json')).read_text());cfg['reservation_retries']=retry
 cfg['source_revision']=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();cfg['source_tree_dirty']=True
 (E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
 r=remote_py(f'from pathlib import Path\nPath({(B+"/"+a+".json")!r}).write_text({json.dumps(cfg)!r})')
 assert r.returncode==0,r.stderr
 r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+shlex.quote(a+'.json'),True)
 (E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
 recover(a)
