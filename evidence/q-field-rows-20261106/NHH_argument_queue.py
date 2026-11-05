from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
queue=[(35,'cm_inverse_log',False,'ARG_CM',False),(36,'cm_inverse_log',True,'ARG_CM',True),(37,'qm_try_log',False,'ARG_Q',False),(38,'qm_try_log',True,'ARG_Q',True),(39,'qm_inv_log',False,'ARG_Q',False),(40,'qm_inv_log',True,'ARG_Q',True),(41,'copy_control',False,'ARG_CM',False),(42,'copy_control',True,'ARG_CM',False),(43,'copy_control',False,'ARG_Q',False),(44,'copy_control',True,'ARG_Q',False)]
for num,target,neg,payload,badarg in queue:
 env=dict(os.environ,NHH_INPUT_SET=str(E/f'NHH_{payload}_INPUTS.json'),NHH_PIN_SET=str(E/f'NHH_{payload}_PINS.json'));env.pop('NHH_INVERT',None);env.pop('NHH_BADARG',None)
 if neg:env['NHH_BADARG'if badarg else'NHH_INVERT']='1'
 a=f'NHH_K{num:03}';r=subprocess.run(['python3',str(E/'NHH_run.py'),a,'kani','NHH_fields::'+target],env=env)
 p=E/a/'stdout.log';s=p.read_text()if p.exists()else''
 assert ('VERIFICATION:- FAILED'in s)if neg else('VERIFICATION:- SUCCESSFUL'in s),(a,'Review before another launch')
