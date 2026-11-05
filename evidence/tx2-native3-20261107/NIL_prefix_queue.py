from pathlib import Path
import subprocess,os,json,sys
E=Path(__file__).resolve().parent
rows=json.loads((E/'NIL_PREFIX_MATRIX.json').read_text());attempt=89
for i,row in enumerate([rows[j] for j in [1,2,4,6,7,8,9,10,11]]):
 for mode in ['positive','control','rename']:
  a=f'NIL_K{attempt:03}';attempt+=1
  env=dict(os.environ)
  if mode=='control':env['NIL_INVERT']='1'
  target=row['rename'] if mode=='rename' else row['function']
  if not (E/a/'receipt.json').exists():
   r=subprocess.run([sys.executable,str(E/'NIL_run.py'),a,'kani',target],env=env,capture_output=True,text=True)
   (E/(a+'-queue.log')).write_text(r.stdout+r.stderr)
  row[mode]=a
  rc=E/a/'receipt.json'
  if not rc.exists():raise RuntimeError('No receipt: '+a)
  x=json.loads(rc.read_text());s=(E/a/'stdout.log').read_text()
  good=x['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in s if mode!='control' else x['exit_status']!=0 and 'VERIFICATION:- FAILED' in s and ('assertion' in s.lower() or 'core::panicking::assert_failed_inner' in s) and 'unwinding assertion' not in s.lower()
  row.setdefault('checks',{})[mode]=good
  (E/'NIL_PREFIX_MATRIX.json').write_text(json.dumps(rows,indent=2)+'\n')
  print(a,mode,x['exit_status'],good,flush=True)
  if not good:raise RuntimeError('unselected failure; isolate before more native work: '+a)
 row['status']='qualified local value facet, parent OPEN'
 (E/'NIL_PREFIX_MATRIX.json').write_text(json.dumps(rows,indent=2)+'\n')
