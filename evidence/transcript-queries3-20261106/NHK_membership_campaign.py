"""Continue independent missing domains, one scope at a time; never retry a receipt."""
from pathlib import Path
import subprocess,json,sys,os,time
E=Path(__file__).resolve().parent
while (E/'NHK_CLIENT_ACTIVE').exists():time.sleep(2)
number=2
rows=[]
for length in [11,12,13,14,15,19,20,21]:
 if length==11:
  a='NHK_K001';r=json.loads((E/a/'receipt.json').read_text())
 else:
  subprocess.run([sys.executable,str(E/'NHK_make_constant_contains.py'),str(length)],check=True)
  subprocess.run([sys.executable,str(E/'NHK_prepare_native.py')],check=True,stdout=subprocess.DEVNULL)
  a=f'NHK_K{number:03}';number+=1
  with (E/(a+'-client.log')).open('w') as f:subprocess.run([sys.executable,str(E/'NHK_run.py'),a,'kani','r0_transcript::NHK_harness::NHK_contains_contract'],stdout=f,stderr=subprocess.STDOUT)
  assert (E/a/'receipt.json').exists(),a+' missing receipt; recover only'
  r=json.loads((E/a/'receipt.json').read_text())
 row=dict(length=length,positive=a,exit=r['exit_status'],status='OPEN')
 if r['exit_status']==0:
  control=f'NHK_K{number:03}';number+=1
  with (E/(control+'-client.log')).open('w') as f:subprocess.run([sys.executable,str(E/'NHK_run.py'),control,'kani','r0_transcript::NHK_harness::NHK_contains_contract'],env=dict(os.environ,NHK_INVERT='1'),stdout=f,stderr=subprocess.STDOUT)
  assert (E/control/'receipt.json').exists(),control+' missing receipt'
  raw=(E/control/'stdout.log').read_text();rc=json.loads((E/control/'receipt.json').read_text())
  row['control']=control;row['control_exit']=rc['exit_status']
  if rc['exit_status']!=0 and 'Failed Checks: |out| *out==expected' in raw and 'timed out' not in raw and 'CBMC failed' not in raw:row['status']='CHECKED_LOCAL_CALLEE'
 rows.append(row);(E/'NHK_MEMBERSHIP_PROGRESS.json').write_text(json.dumps(rows,indent=2)+'\n');print(json.dumps(row),flush=True)
print('NEXT_ATTEMPT',number,flush=True)
