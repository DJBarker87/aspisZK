from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
for num,target,neg in [(73,'cm_zero_panic',False),(74,'cm_zero_panic',True),(75,'cm_zero_prefix',False),(76,'cm_zero_prefix',True),(77,'copy_control',False),(78,'copy_control',True)]:
 env=dict(os.environ,NHH_INPUT_SET=str(E/'NHH_CM_ZERO_INPUTS.json'),NHH_PIN_SET=str(E/'NHH_CM_ZERO_PINS.json'));env.pop('NHH_INVERT',None);env.pop('NHH_BADARG',None)
 if neg:env['NHH_INVERT']='1'
 a=f'NHH_K{num:03}';r=subprocess.run(['python3',str(E/'NHH_run.py'),a,'kani','NHH_fields::'+target],env=env)
 s=(E/a/'stdout.log').read_text();assert ('VERIFICATION:- FAILED'in s)if neg else('VERIFICATION:- SUCCESSFUL'in s),(a,'Review before another launch')
