from pathlib import Path
import subprocess,os,json
E=Path(__file__).resolve().parent
queue=[(8,'m31_embed',True),(9,'cm31_embed',False),(10,'cm31_embed',True),(11,'qm31_embed',False),(12,'qm31_embed',True),(13,'wide_embed',False),(14,'wide_embed',True),(15,'cm_inherent',False),(16,'cm_inherent',True),(17,'qm_neg',False),(18,'qm_neg',True),(19,'copy_control',False),(20,'copy_control',True)]
for num,target,neg in queue:
 env=dict(os.environ);env.pop('NHH_INVERT',None)
 if neg:env['NHH_INVERT']='1'
 a=f'NHH_K{num:03}';r=subprocess.run(['python3',str(E/'NHH_run.py'),a,'kani','NHH_fields::'+target],env=env)
 p=E/a/'stdout.log';s=p.read_text() if p.exists() else ''
 assert ('VERIFICATION:- FAILED' in s) if neg else ('VERIFICATION:- SUCCESSFUL' in s),(a,'Review failure; never proceed on timeout')
