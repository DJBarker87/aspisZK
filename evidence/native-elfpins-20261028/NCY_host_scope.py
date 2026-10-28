"""Task wrapper: admission plus an existing capped runner; no shared infrastructure edits."""
import subprocess,shlex,json,pathlib,sys,time,hashlib
E=pathlib.Path(__file__).parent
H='/home/dombarker/project-offloads/codex-cx-native-elfpins-20261028'
remote='dombarker@100.108.41.90'
label=sys.argv[1];code=pathlib.Path(sys.argv[2]).read_text()
def ssh(c):return subprocess.run(['ssh','-o','ConnectTimeout=15',remote,c],capture_output=True,text=True)
for trial in range(11):
 init=f'''import pathlib,subprocess,json,sys
h=pathlib.Path({H!r});h.mkdir(exist_ok=True)
p=h/{(label+'-barrier-'+str(trial)+'.log')!r}
with p.open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(h/{(label+'-reservation.json')!r})],stdout=f,stderr=subprocess.STDOUT)
print(p.read_text());sys.exit(r.returncode)
'''
 r=ssh('python3 -c '+shlex.quote(init));(E/(label+f'-barrier-{trial}.log')).write_text(r.stdout+r.stderr)
 if r.returncode==255:
  if trial<10:time.sleep(60);continue
  raise SystemExit('transport exhausted')
 try:ad=next(json.loads(l) for l in r.stdout.splitlines() if l.startswith('{'))
 except (ValueError,StopIteration):
  if trial==0:time.sleep(30);continue
  raise SystemExit('missing admission')
 (E/(label+'-reservation.json')).write_text(json.dumps(ad,indent=2)+'\n')
 if r.returncode==0 and ad.get('allowed') is True:break
 if (r.returncode==78 or ad.get('allowed') is False) and trial<10:time.sleep(180);continue
 raise SystemExit('admission failed')
else:raise SystemExit('admission exhausted')
pins=(E/'NCY_SOURCE_PINS.json').read_text()
u=subprocess.run(['ssh','-o','ConnectTimeout=15',remote,'cat > '+shlex.quote(H+'/NCY_SOURCE_PINS.json')],input=pins,capture_output=True,text=True)
assert u.returncode==0,u.stderr
u=ssh('python3 -c '+shlex.quote(f'from pathlib import Path;Path({(H+"/"+label+".py")!r}).write_text({code!r})'))
assert u.returncode==0,u.stderr
cmd=['systemd-run','--user','--scope','--quiet','--unit='+label,'-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','/usr/bin/time','-v','-o',H+'/'+label+'-time.log','timeout','600','python3',H+'/'+label+'.py']
t0=time.monotonic();r=ssh(shlex.join(cmd));elapsed=time.monotonic()-t0
(E/(label+'-launch.log')).write_text(r.stdout+r.stderr)
assert r.returncode!=255,'Submitted transport lost: recover read-only; never resubmit'
q=ssh('cat '+shlex.quote(H+'/'+label+'-time.log'));assert q.returncode==0,q.stderr
(E/(label+'-time.log')).write_text(q.stdout)
(E/(label+'-stdout.log')).write_text(r.stdout)
(E/(label+'-stderr.log')).write_text(r.stderr)
import re
rss=re.search(r'Maximum resident set size \(kbytes\): (\d+)',q.stdout)
swaps=re.search(r'Swaps: (\d+)',q.stdout)
j=dict(attempt=label,exit_status=r.returncode,wall_seconds_transport_included=elapsed,peak_rss_kib=int(rss[1]) if rss else None,swaps=int(swaps[1]) if swaps else None,scope_command=cmd,actual_task_revision=subprocess.check_output(['git','rev-parse','HEAD']).decode().strip(),source_sha256=hashlib.sha256(code.encode()).hexdigest(), print_axioms='N/A: no Lean',admission_allowed=True,admission_exit=0)
(E/(label+'-receipt.json')).write_text(json.dumps(j,indent=2)+'\n')
with (E/'NCY_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(j)+'\n')
out={'stdout.log':r.stdout,'stderr.log':r.stderr}
print(json.dumps(j,indent=2));print(out.get('stdout.log',''));print(out.get('stderr.log',''))
