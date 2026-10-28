"""Task wrapper: admission plus an existing capped runner; no shared infrastructure edits."""
import subprocess,shlex,json,pathlib,sys,time
E=pathlib.Path(__file__).parent
H='/home/dombarker/project-offloads/codex-cx-native-elfscope-20261028'
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
u=ssh('python3 -c '+shlex.quote(f'from pathlib import Path;Path({(H+"/"+label+".py")!r}).write_text({code!r})'))
assert u.returncode==0,u.stderr
cmd=['systemd-run','--user','--scope','--quiet','--unit='+label,'-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3','/home/dombarker/project-offloads/codex-cx-pin-20261020/harness/capped.py',H+'/'+label,'Pinned source and SDK inspection or optimized SBF release compilation; no Kani or Lean','--','timeout','240','python3',H+'/'+label+'.py']
r=ssh(shlex.join(cmd));(E/(label+'-launch.log')).write_text(r.stdout+r.stderr)
# Never resubmit after submission. Recover existing receipts only.
for retry in range(11):
 q=ssh('python3 -c '+shlex.quote(f'import pathlib,json;h=pathlib.Path({(H+"/"+label)!r});print(json.dumps({{n:(h/n).read_text() for n in ["receipt.json","stdout.log","stderr.log","time.log"] if (h/n).exists()}}))'))
 if q.returncode==0:break
 if q.returncode!=255 or retry==10:raise SystemExit('recovery failed')
 time.sleep(60)
out=json.loads(q.stdout);assert 'receipt.json' in out,'missing submitted receipt'
for n,s in out.items():(E/(label+'-'+n)).write_text(s)
j=json.loads(out['receipt.json']);j.update(attempt=label,actual_task_revision=subprocess.check_output(['git','rev-parse','HEAD']).decode().strip(),scope_command=cmd)
with (E/'NCR_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(j)+'\n')
print(json.dumps(j,indent=2));print(out.get('stdout.log',''));print(out.get('stderr.log',''))
