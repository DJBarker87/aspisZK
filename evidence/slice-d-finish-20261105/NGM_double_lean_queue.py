from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
jobs=['NGM_LPf_ReductionWord','NGM_LPf_CoreReduction','NGM_LPf_BaseMultiply','NGM_LPi_Total','NGM_LPi_NatBase','NGM_LPi_CMProduct','NGM_LPi_FieldValues','NGM_LPi_TowerValues','NGM_ProbeTransport','NGM_ScalarCanon','NGM_AddReference','NGM_ReferenceLinear','NGM_DoubleModel','NGM_DoubleProduct']
for target in jobs:
 used=[int(p.parent.name[-3:])for p in E.glob('NGM_L*/receipt.json')];a=f'NGM_L{max(used,default=0)+1:03}'
 r=subprocess.run([sys.executable,str(E/'NGM_run.py'),a,'lean',target],capture_output=True,text=True)
 (E/(a+'-queue.log')).write_text(r.stdout+r.stderr);p=E/a/'receipt.json'
 if not p.exists():raise SystemExit('Missing receipt: '+r.stdout[-1500:]+r.stderr[-1000:])
 x=json.loads(p.read_text());print(json.dumps({k:x[k]for k in ['attempt','module','exit_status','wall_seconds','peak_rss_kib']}),flush=True)
 if x['exit_status']:raise SystemExit(r.stdout[-2500:]+r.stderr[-1000:])
