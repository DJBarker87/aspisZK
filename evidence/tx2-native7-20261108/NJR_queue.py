from pathlib import Path
import subprocess,os,json
E=Path(__file__).resolve().parent
jobs=[(5,'pending_destination','BAD_DESTINATION'),(6,'pending_destination','INVERT'),(7,'reader_backing',None),(8,'reader_backing','BAD_BACKING'),(9,'reader_backing','BAD_DROP'),(10,'reader_backing','INVERT'),(11,'flush_receiver',None),(12,'flush_receiver','BAD_RECEIVER'),(13,'flush_receiver','INVERT')]
for number,name,control in jobs:
 env=os.environ.copy()
 if control:env['NJR_'+control]='1'
 a=f'NJR_K{number:03d}'
 r=subprocess.run(['python3',str(E/'NJR_run.py'),a,'kani','verifier::NJR_parent::'+name],env=env)
 raw=(E/a/'stdout.log').read_text()
 if 'timed out' in raw or 'Timed out' in raw:raise RuntimeError((a,'timeout; isolate before follow-ups'))
 if (r.returncode==0)!=(control is None):raise RuntimeError((a,r.returncode))
 if control and 'VERIFICATION:- FAILED' not in raw:raise RuntimeError((a,'not a semantic control'))
