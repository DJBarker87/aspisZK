from pathlib import Path
import json,subprocess,sys,shlex,time
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin36-20261028';H='/home/dombarker/project-offloads/codex-pv-runjoin-20261026';W=H+'/runjoin36-extraction';host='dombarker@100.108.41.90';phase=sys.argv[1]
assert not (E/phase).exists(),'recover logs instead of resubmission'
def ssh(s):return subprocess.run(['ssh',host,s],capture_output=True,text=True)
r=ssh(f'python3 {H}/reservation-existing.py {W}/reservation-{phase}.json > {W}/reservation-{phase}.log 2>&1\nstatus=$?\ncat {W}/reservation-{phase}.log\nexit $status');(E/f'reservation-{phase}-{time.time_ns()}.log').write_text(r.stdout+r.stderr)
a=json.loads(r.stdout.strip().splitlines()[-1]);assert r.returncode==0 and a.get('allowed'),('REFUSAL unlaunched',r.returncode,a)
for src,dest in [(R/'tools/pv-runjoin36-20261028/capped.py',W+'/capped.py'),(E/(phase+'-command.json'),W+'/'+phase+'-command.json')]:subprocess.run(['scp','-q',str(src),host+':'+dest],check=True)
spec=json.load(open(E/(phase+'-command.json')))
cmd=['systemd-run','--user','--scope','--quiet','--unit=pv36-'+phase,'-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',W+'/capped.py',W,phase]
(E/(phase+'-submission.json')).write_text(json.dumps(dict(scope_command=cmd,admission=a,**spec),indent=2)+'\n')
r=ssh(shlex.join(cmd));(E/(phase+'-scope.log')).write_text(r.stdout+r.stderr)
subprocess.run(['scp','-qr',host+':'+W+'/'+phase,str(E)],check=True)
print(r.stdout+r.stderr);sys.exit(r.returncode)
