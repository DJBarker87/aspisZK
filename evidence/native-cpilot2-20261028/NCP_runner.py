"""Own serial controller: frozen scratch only; unchanged admission/backend."""
from pathlib import Path
import subprocess,json,sys,time,shlex,hashlib,tomllib
E=Path(__file__).resolve().parent
H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-native-cpilot2-20261028'
REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
def ssh(code,submitted=False):
 for n in range(11):
  r=subprocess.run(['ssh','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2',H,code],capture_output=True,text=True)
  with (E/'NCP_NATIVE_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(trial=n,exit=r.returncode,submitted=submitted,stdout=(r.stdout if len(r.stdout)<120000 else {'sha256':hashlib.sha256(r.stdout.encode()).hexdigest(),'bytes':len(r.stdout.encode()),'retained_on_host':True}),stderr=r.stderr,command=code))+'\n')
  if r.returncode!=255 or submitted:return r
  if n<10:time.sleep(60)
 raise SystemExit('STOP transport exhausted')
def py(s,**kw):return ssh('python3 -c '+shlex.quote(s),**kw)
def admit(a):
 for n in range(11):
  s=f'''from pathlib import Path
import subprocess,json
b=Path({B!r}); b.mkdir(exist_ok=True)
p=b/{(a+'-barrier-'+str(n)+'.log')!r}
with p.open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/{(a+'-reservation.json')!r})],stdout=f,stderr=subprocess.STDOUT)
print(json.dumps(dict(exit=r.returncode,log=p.read_text(),reservation=json.loads((b/{(a+'-reservation.json')!r}).read_text()) if (b/{(a+'-reservation.json')!r}).exists() else None)))
'''
  r=py(s);assert r.returncode==0,r.stderr
  x=json.loads(r.stdout);(E/(a+f'-admission-{n}.json')).write_text(json.dumps(x,indent=2)+'\n')
  if x['reservation'] is None:
   if n==0:time.sleep(30);continue
   raise SystemExit('STOP missing reservation JSON')
  if x['exit']==0 and x['reservation'].get('allowed') is True:return
  if (x['exit']==78 or x['reservation'].get('allowed') is False) and n<10:time.sleep(180);continue
  raise SystemExit('STOP admission')
 raise SystemExit('STOP admission exhausted')
def collect(a):
 r=py(f'''from pathlib import Path
import json
b=Path({B!r}); print(json.dumps({{n:(b/n).read_text() for n in {[a+'/receipt.json',a+'/stdout.log',a+'/time.log']!r} if (b/n).exists()}}))''');assert r.returncode==0
 x=json.loads(r.stdout)
 for n,s in x.items():p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
 assert a+'/receipt.json' in x,'STOP unresolved submitted run, do not resubmit'
 receipt=json.loads(x[a+'/receipt.json'])
 with (E/'NCP_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(receipt)+'\n')
 return receipt
def launch(a,kind,command,sources,timeout=180):
 admit(a)
 preflight=py('from pathlib import Path; b=Path('+repr(B)+'); missing=[f for f in '+repr(sources)+' if not (b/f).is_file()]; assert not missing,missing')
 assert preflight.returncode==0,preflight.stdout+preflight.stderr
 target=command[command.index('--harness')+1] if '--harness' in command else 'cargo metadata'
 cfg=dict(attempt=a,kind=kind,module=target,sources=sources,command=command,timeout=timeout,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,env={'PATH':'/home/dombarker/.cargo/bin:/usr/bin:/bin','CARGO_NET_OFFLINE':'true','CARGO_BUILD_JOBS':'1','CARGO_PROFILE_DEV_OPT_LEVEL':'3','CARGO_PROFILE_DEV_DEBUG':'0','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS':'true','CARGO_TARGET_DIR':B+'/NCP_target','TMPDIR':B+'/NCP_tmp'},deps_fingerprint={'frozen_source':REV},expected_time='Optimized compilation, then '+target+' solver gate; no field multiplication or protocol whole-buffer loop')
 (E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
 r=py(f'from pathlib import Path; p=Path({(B+"/"+a+".json")!r}); p.write_text({json.dumps(cfg,indent=2)!r})');assert r.returncode==0
 r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+shlex.quote(a+'.json'),submitted=True)
 (E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
 rc=collect(a);print(a,rc['exit_status'],rc['wall_seconds'],rc['peak_rss_kib'],flush=True);return rc
