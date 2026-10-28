from pathlib import Path
import subprocess,sys,os,json
E=Path(__file__).resolve().parent
rows=[('NCO_K030','kani','compact::NCO_compact::compact_row_caller',None),('NCO_K031','kani','compact::NCO_compact::compact_row_wrong',None),('NCO_K032','kani','compact::NCO_compact::compact_row_contract','NCO_invert_compact')]
rows += [(f'NCO_K{i:03}','kani','NCO_controls::'+t,None) for i,t in enumerate(['option_positive','option_real','option_unimplied','option_negative','option_frame'],33)]
rows += [('NCO_L001','lean','NCO_Reference/Types',None),('NCO_L002','lean','NCO_Reference/Funs',None)]
for a,k,t,cfg in rows:
 env=dict(os.environ)
 if cfg:env['NCO_RUST_CFG']=cfg
 r=subprocess.run([sys.executable,str(E/'NCO_run.py'),a,k,t],env=env)
 if r.returncode:raise SystemExit(r.returncode)
 receipt=json.loads((E/a/'receipt.json').read_text())
 if k=='lean' and receipt['exit_status']!=0:raise SystemExit('Lean dependency failed')
