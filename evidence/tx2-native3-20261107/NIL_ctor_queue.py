from pathlib import Path
import os,json,subprocess,sys
E=Path(__file__).resolve().parent
row=json.loads((E/'NIL_CTOR_PLAN.json').read_text())
for mode,a,flag,target in [('positive',row['positive'],None,row['function']),('control_value',row['control_value'],'NIL_BAD_BOX_VALUE',row['function']),('control_allocation',row['control_allocation'],'NIL_BAD_ALLOC',row['function']),('rename',row['rename_attempt'],None,row['rename'])]:
 env=dict(os.environ)
 if flag:env[flag]='1'
 r=subprocess.run([sys.executable,str(E/'NIL_run.py'),a,'kani',target],env=env,capture_output=True,text=True)
 (E/(a+'-queue.log')).write_text(r.stdout+r.stderr)
 x=json.loads((E/a/'receipt.json').read_text());s=(E/a/'stdout.log').read_text()
 good=x['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in s if flag is None else x['exit_status']!=0 and 'VERIFICATION:- FAILED' in s and ('assertion' in s.lower() or 'core::panicking::assert_failed_inner' in s) and 'unwinding assertion' not in s.lower()
 row.setdefault('checks',{})[mode]=good
 (E/'NIL_CTOR_PLAN.json').write_text(json.dumps(row,indent=2)+'\n')
 print(a,mode,x['exit_status'],good,flush=True)
 if not good:raise RuntimeError('isolate '+a)
row['status']='qualified local allocation/payload facet, full resume OPEN'
(E/'NIL_CTOR_PLAN.json').write_text(json.dumps(row,indent=2)+'\n')
