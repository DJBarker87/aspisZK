from pathlib import Path
import subprocess,os,json
E=Path(__file__).resolve().parent
q=[(46,'m31_embed',1,'BASE','invert'),(47,'cm31_embed',0,'BASE',''),(48,'cm31_embed',1,'BASE','invert'),(49,'qm31_embed',0,'BASE',''),(50,'qm31_embed',1,'BASE','invert'),(51,'wide_embed',0,'BASE',''),(52,'wide_embed',1,'BASE','invert'),(53,'cm_inherent',0,'BASE',''),(54,'cm_inherent',1,'BASE','invert'),(55,'qm_neg',0,'BASE',''),(56,'qm_neg',1,'BASE','invert'),(57,'copy_control',0,'BASE',''),(58,'copy_control',1,'BASE','invert'),(59,'cm_inverse_log',0,'ARG_CM',''),(60,'cm_inverse_log',1,'ARG_CM','bad_argument'),(61,'qm_try_log',0,'ARG_Q',''),(62,'qm_try_log',1,'ARG_Q','bad_argument'),(63,'qm_inv_log',0,'ARG_Q',''),(64,'qm_inv_log',1,'ARG_Q','bad_argument'),(65,'copy_control',0,'ARG_CM',''),(66,'copy_control',1,'ARG_CM','invert'),(67,'copy_control',0,'ARG_Q',''),(68,'copy_control',1,'ARG_Q','invert'),(69,'qm_zero_none',0,'ARG_Q',''),(70,'qm_zero_none',1,'ARG_Q','invert'),(71,'qm_zero_panic',0,'ARG_Q',''),(72,'qm_zero_panic',1,'ARG_Q','invert')]
for num,target,neg,payload,flag in q:
 env=dict(os.environ);env.pop('NHH_INVERT',None);env.pop('NHH_BADARG',None)
 if payload!='BASE':env.update(NHH_INPUT_SET=str(E/f'NHH_{payload}_INPUTS.json'),NHH_PIN_SET=str(E/f'NHH_{payload}_PINS.json'))
 if flag:env['NHH_BADARG'if flag=='bad_argument'else'NHH_INVERT']='1'
 a=f'NHH_K{num:03}';r=subprocess.run(['python3',str(E/'NHH_run.py'),a,'kani','NHH_fields::'+target],env=env)
 p=E/a/'stdout.log';s=p.read_text()if p.exists()else''
 assert ('VERIFICATION:- FAILED'in s)if neg else('VERIFICATION:- SUCCESSFUL'in s),(a,'Review before another launch')
 sc=json.loads((E/(a+'-source-check.json')).read_text());assert sc['frozen_files']==735 and not sc['errors']
