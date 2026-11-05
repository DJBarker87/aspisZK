"""Bottom-up scalar membership on arbitrary-offset native windows."""
from pathlib import Path
import json,subprocess,os,sys
E=Path(__file__).resolve().parent;number=int(sys.argv[1]);rows=[]
assert not (E/'NHK_CLIENT_ACTIVE').exists()
for width in [1,3,4,5,6,7,8]:
 subprocess.run([sys.executable,str(E/'NHK_make_window.py'),'22',str(width)],check=True)
 subprocess.run([sys.executable,str(E/'NHK_prepare_native.py')],check=True,stdout=subprocess.DEVNULL)
 row=dict(length=22,width=width,status='OPEN')
 for invert in [False,True]:
  a=f'NHK_K{number:03}';number+=1
  with (E/(a+'-client.log')).open('w') as f:subprocess.run([sys.executable,str(E/'NHK_run.py'),a,'kani','r0_transcript::NHK_harness::NHK_contains_contract'],env=dict(os.environ,**({'NHK_INVERT':'1'} if invert else {})),stdout=f,stderr=subprocess.STDOUT)
  assert (E/a/'receipt.json').exists(),a+' missing receipt, recover only'
  r=json.loads((E/a/'receipt.json').read_text());raw=(E/a/'stdout.log').read_text()
  row['control' if invert else 'positive']=a
  good=(r['exit_status']!=0 and 'Failed Checks:' in raw and 'result == expected' in raw and 'timed out' not in raw and 'CBMC failed' not in raw) if invert else r['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in raw
  if not good:break
  if invert:row['status']='CHECKED_SCALAR_WINDOW'
 rows.append(row);(E/'NHK_WINDOW_PROGRESS.json').write_text(json.dumps(rows,indent=2)+'\n');print(json.dumps(row),flush=True)
print('NEXT_ATTEMPT',number,flush=True)
