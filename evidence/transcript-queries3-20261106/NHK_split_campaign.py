"""Serial changed-shape window gates. This script never launches concurrently."""
from pathlib import Path
import json,subprocess,os,sys
E=Path(__file__).resolve().parent
number=int(sys.argv[1]);rows=[]
assert not (E/'NHK_CLIENT_ACTIVE').exists()
# Establish full-source contiguous splits for every missing length first.
checked={r['length'] for r in json.loads((E/'NHK_MEMBERSHIP_PROGRESS.json').read_text()) if r['status']=='CHECKED_LOCAL_CALLEE'}
for n in [11,12,13,14,15,17,19,20,21,9]:
 if n in checked:continue
 subprocess.run([sys.executable,str(E/'NHK_make_native_split.py'),str(n),'8'],check=True)
 subprocess.run([sys.executable,str(E/'NHK_prepare_native.py')],check=True,stdout=subprocess.DEVNULL)
 row=dict(length=n,cut=8,status='OPEN')
 for invert in [False,True]:
  a=f'NHK_K{number:03}';number+=1
  with (E/(a+'-client.log')).open('w') as f:subprocess.run([sys.executable,str(E/'NHK_run.py'),a,'kani','r0_transcript::NHK_harness::NHK_contains_contract'],env=dict(os.environ,**({'NHK_INVERT':'1'} if invert else {})),stdout=f,stderr=subprocess.STDOUT)
  assert (E/a/'receipt.json').exists(),a+' missing receipt, recover only'
  r=json.loads((E/a/'receipt.json').read_text());raw=(E/a/'stdout.log').read_text()
  row['control' if invert else 'positive']=a
  good=(r['exit_status']!=0 and 'Failed Checks:' in raw and 'result ==' in raw and 'timed out' not in raw and 'CBMC failed' not in raw) if invert else r['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in raw
  if not good:break
  if invert:row['status']='CHECKED_NATIVE_SPLIT'
 rows.append(row);(E/'NHK_SPLIT_PROGRESS.json').write_text(json.dumps(rows,indent=2)+'\n');print(json.dumps(row),flush=True)
print('NEXT_ATTEMPT',number,flush=True)
