"""Serial focused module schedule, stopping on the first failing declaration."""
from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent
D=E/'NNH_dependency_inputs';D.mkdir(exist_ok=True)
# RSL frozen revision-2 sources are staged unchanged, never edited.
rsl=['RSL_Base','RSL_Pool','RSL_TX2_217','RSL_TX2_234','RSL_TX2_233','RSL_TX2_242','RSL_TX2_241','RSL_TX2_240','RSL_TX2_221','RSL_TX2_213','RSL_Verifier','RSL_TX1_136','RSL_TX1_137','RSL_TX1_087','RSL_TX1_094','RSL_TX1_328','RSL_TX1_345','RSL_TX1_344','RSL_TX1_333','RSL_TX1_330']
for n in rsl:(D/(n+'.lean')).write_bytes((E.parent/'rowspec-lead-20261107'/(n+'.lean')).read_bytes())
plan=rsl+['NNH_NoWritePool','NNH_NoWriteOwned','NNH_NoWrite241','NNH_Rev2Support','NNH_RSLAuth','NNH_RSLReads']
(E/'NNH_STAGE1_PLAN.json').write_text(json.dumps(plan,indent=1)+'\n')
for i,n in enumerate(plan,1):
 a=f'NNH_L{i:03}'
 if (E/a/'receipt.json').exists():
  assert json.loads((E/a/'receipt.json').read_text())['exit_status']==0
  continue
 r=subprocess.run(['python3',str(E/'NNH_run.py'),a,'lean',n])
 if r.returncode:raise SystemExit(r.returncode)
