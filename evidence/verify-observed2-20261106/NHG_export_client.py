"""Owned serial file-packaging client. No formal budget invocation."""
from pathlib import Path
import subprocess,json,time,shlex,re,hashlib
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-verify-observed2-20261106'
assert not(E/'NHG_CLIENT_ACTIVE').exists()
def ssh(command,data=None,submitted=False):
 for i in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,command],input=data,text=True,capture_output=True)
  with(E/'NHG_EXPORT_TRANSPORT.jsonl').open('a')as f:f.write(json.dumps(dict(retry=i,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
  if r.returncode!=255:return r
  if submitted:raise RuntimeError('Submitted packaging scope: recover read-only, never resubmit')
  if i<10:time.sleep(60)
 raise RuntimeError('Transport unavailable')
for i in range(11):
 code=f'''from pathlib import Path
import subprocess,sys
p=Path({B!r})/'NHG_EXPORT-reservation.json'
with open({(B+'/NHG_EXPORT-barrier-'+str(i)+'.log')!r},'w')as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(p)],stdout=f,stderr=subprocess.STDOUT)
print(p.read_text()if p.exists()else'MISSING');sys.exit(r.returncode)
'''
 r=ssh('python3',code);(E/f'NHG_EXPORT-barrier-{i}.log').write_text(r.stdout+r.stderr)
 try:reservation=json.loads(r.stdout)
 except json.JSONDecodeError:
  if i==0:time.sleep(30);continue
  raise
 (E/'NHG_EXPORT_ADMISSION.json').write_text(json.dumps(dict(exit=r.returncode,reservation=reservation)))
 if r.returncode==0 and reservation.get('allowed')is True:break
 if(r.returncode==78 or reservation.get('allowed')is False)and i<10:
  for _ in range(3):time.sleep(60)
  continue
 raise RuntimeError('Admission refused')
modules=list(dict.fromkeys(re.findall(r'^import (NHG_\w+)',(E/'NHG_COMBINED_IMPORT.lean').read_text(),re.M)+['NHG_COMBINED_IMPORT']))
inputs=dict(modules=modules,lean_path=json.loads((E/'NHG_PATHS.json').read_text()))
(E/'NHG_FINAL_EXPORT_INPUT.json').write_text(json.dumps(inputs,indent=1)+'\n')
files={'NHG_export_io.py':(E/'NHG_export_io.py').read_text(),'NHG_FINAL_EXPORT_INPUT.json':json.dumps(inputs)}
code=f'''from pathlib import Path
import json
b=Path({B!r})
for n,t in json.loads({json.dumps(files)!r}).items():(b/n).write_text(t)
''';r=ssh('python3',code);assert r.returncode==0,r.stderr
command='cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 /usr/bin/time -v -o NHG_EXPORT.time python3 NHG_export_io.py'
r=ssh(command,submitted=True);(E/'NHG_EXPORT-launcher.log').write_text(r.stdout+r.stderr);assert r.returncode==0,r.stderr
code=f'''from pathlib import Path
import json,base64
b=Path({B!r});names=['NHG_EXPORT.json','NHG_EXPORT.time','NHG_FINAL_CLOSURE_PINS.json.sha256','NHG_FINAL_CLOSURE_PINS.json.xz']
print(json.dumps({{n:base64.b64encode((b/n).read_bytes()).decode()for n in names}}))
''';r=ssh('python3',code);assert r.returncode==0
import base64
for n,v in json.loads(r.stdout).items():(E/n).write_bytes(base64.b64decode(v))
print((E/'NHG_EXPORT-launcher.log').read_text()[:1500])
