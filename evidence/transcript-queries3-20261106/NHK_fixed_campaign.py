"""Serial, full-domain fixed-prefix membership checks with matched controls."""
from pathlib import Path
import json,subprocess,os,sys
E=Path(__file__).resolve().parent;number=20
rows=[dict(length=11,cut=8,status='CHECKED_LOCAL_CALLEE',positive='NHK_K018',control='NHK_K019')]
for n in [12,13,14,15,17,20,21]:
 subprocess.run([sys.executable,str(E/'NHK_make_fixed.py'),str(n)],check=True)
 subprocess.run([sys.executable,str(E/'NHK_prepare_native.py')],check=True,stdout=subprocess.DEVNULL)
 row=dict(length=n,cut=8,status='OPEN')
 for invert in [False,True]:
  a=f'NHK_K{number:03}';number+=1
  with (E/(a+'-client.log')).open('w') as f:subprocess.run([sys.executable,str(E/'NHK_run.py'),a,'kani','r0_transcript::NHK_harness::NHK_contains_contract'],env=dict(os.environ,**({'NHK_INVERT':'1'} if invert else {})),stdout=f,stderr=subprocess.STDOUT)
  assert (E/a/'receipt.json').exists(),a+' missing receipt, recover only'
  r=json.loads((E/a/'receipt.json').read_text());raw=(E/a/'stdout.log').read_text();row['control' if invert else 'positive']=a
  good=(r['exit_status']!=0 and 'Failed Checks: assertion failed: result == expected' in raw and 'timed out' not in raw and 'CBMC failed' not in raw) if invert else r['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in raw
  if not good:break
  if invert:row['status']='CHECKED_LOCAL_CALLEE'
 rows.append(row);(E/'NHK_FIXED_PROGRESS.json').write_text(json.dumps(rows,indent=2)+'\n');print(json.dumps(row),flush=True)
print('NEXT_ATTEMPT',number,flush=True)
