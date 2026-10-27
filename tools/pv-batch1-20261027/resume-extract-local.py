"""Task sequencing only: admitted transfer and separately retryable phases."""
import subprocess,time,json
from pathlib import Path
host='dombarker@100.108.41.90';H='/home/dombarker/project-offloads/codex-pv-batch1-20261027';E=Path('evidence/pv-batch1-20261027')
def wait():
 for n in range(3):time.sleep(60);print('Admission wait minute',n+1,flush=True)
# A stage refusal immediately preceded this invocation; a fresh full wait.
for retry in range(1,11):
 wait()
 label=f'resume-extract-stage-retry{retry}'
 r=subprocess.run(['ssh',host,f'cd {H} && python3 Port13GATE_admission.py > reservation-{label}.json 2>&1'],capture_output=True,text=True)
 print(label,r.returncode,flush=True)
 if r.returncode==0:break
else:raise SystemExit('ten stage refusals; continue compile-free and return later')
subprocess.run(['scp','tools/pv-batch1-20261027/extract.py','tools/pv-batch1-20261027/lean.py',host+':'+H+'/'],check=True)
for op in [230,254,258]:
 for phase in ['charon','aeneas']:
  for retry in range(11):
   suffix=f'resume-{phase}-{retry}'
   log=E/f'extract-{op}-{suffix}-launcher.log'
   with log.open('w') as out:
    r=subprocess.run(['ssh',host,f'cd {H} && python3 extract.py {op} {suffix} {phase}'],stdout=out,stderr=subprocess.STDOUT)
   print(op,phase,retry,r.returncode,flush=True)
   if r.returncode==0:break
   if r.returncode==78:wait();continue
   raise SystemExit(log.read_text())
  else:raise SystemExit('ten phase refusals; continue compile-free and return later')
