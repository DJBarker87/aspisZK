"""Serialize direct extraction modules, preserving every admission refusal."""
from run import H
import subprocess,json,time
R=H/'resume17'
def invoke(stage,group,ident):
 for retry in range(11):
  p=H/'admission-not-before.json'
  while p.exists() and (left:=json.loads(p.read_text())['epoch']-time.time())>0:time.sleep(min(30,left))
  r=subprocess.run(['python3',str(H/'extract227_resume17_host.py'),stage,group,str(ident)],stdout=(R/f'queue-{ident}-{retry}.log').open('w'),stderr=subprocess.STDOUT)
  print(json.dumps(dict(stage=stage,group=group,id=ident,retry=retry,exit=r.returncode)),flush=True)
  if r.returncode!=78:return r.returncode
 return 78
for i,g in enumerate(['terminal','copy','field','poseidon','statement-copy']):
 c=invoke('charon',g,73900+2*i)
 if c==78:raise SystemExit('admission attempts exhausted')
 if c==0:invoke('aeneas',g,73901+2*i)
