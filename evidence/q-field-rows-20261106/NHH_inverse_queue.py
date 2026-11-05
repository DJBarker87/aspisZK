from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
queue=[(23,'copy_control',False,'INVERSE'),(24,'copy_control',True,'INVERSE'),(25,'qm_try_log',False,'QINVERSE'),(26,'qm_try_log',True,'QINVERSE'),(27,'qm_zero_none',False,'QINVERSE'),(28,'qm_zero_none',True,'QINVERSE'),(29,'qm_zero_panic',False,'QINVERSE'),(30,'qm_zero_panic',True,'QINVERSE'),(31,'copy_control',False,'QINVERSE'),(32,'copy_control',True,'QINVERSE'),(33,'qm_inv_log',False,'QINVERSE'),(34,'qm_inv_log',True,'QINVERSE')]
for num,target,neg,payload in queue:
 env=dict(os.environ,NHH_INPUT_SET=str(E/f'NHH_{payload}_INPUTS.json'),NHH_PIN_SET=str(E/f'NHH_{payload}_PINS.json'));env.pop('NHH_INVERT',None)
 if neg:env['NHH_INVERT']='1'
 a=f'NHH_K{num:03}';r=subprocess.run(['python3',str(E/'NHH_run.py'),a,'kani','NHH_fields::'+target],env=env)
 p=E/a/'stdout.log';s=p.read_text() if p.exists() else ''
 assert ('VERIFICATION:- FAILED' in s) if neg else ('VERIFICATION:- SUCCESSFUL' in s),(a,'Review failure or panic verdict; never proceed on timeout')
