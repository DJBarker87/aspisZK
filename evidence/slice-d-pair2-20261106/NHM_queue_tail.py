from pathlib import Path
import subprocess,os,json
E=Path(__file__).resolve().parent
jobs=[]
for a,name in [(84,'partial'),(85,'high'),(86,'byte')]:jobs.append((a,f'weights::NHM_windows::{name}00',dict(NHM_INVERT='1',NHM_NATIVE_CFG='NHM_corrupt'),True))
number=87
for fam in range(3):
 for control in [False,True]:
  jobs.append((number,f'weights::NHM_group::control{fam:02}',dict(NHM_INVERT='1')if control else{},control));number+=1
for name,count in [('coefficient',5),('weight',5),('accumulate',4)]:
 for g in range(count):
  for control in [False,True]:
   jobs.append((number,f'weights::NHM_group::{name}{g:02}',dict(NHM_INVERT='1')if control else{},control));number+=1
assert number==121
for number,harness,flags,negative in jobs:
 a=f'NHM_K{number:03}'
 r=subprocess.run(['python3',str(E/'NHM_run.py'),a,'kani',harness],env=dict(os.environ,**flags))
 log=(E/a/'stdout.log').read_text()
 assert ('VERIFICATION:- FAILED'if negative else'VERIFICATION:- SUCCESSFUL')in log and 'timed out'not in log.lower()and'unwinding failures'not in log,(a,r.returncode)
