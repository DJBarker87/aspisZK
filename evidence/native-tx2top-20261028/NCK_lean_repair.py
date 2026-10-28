from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent;R=E.parents[1]
modules=['NCK_Stage2Cuts','NCK_ScanDependency','NCK_Stage2Shape','NCK_Admission','NCK_CheckpointMeta','NCK_SnapshotRead','NCK_SecondBinding','NCK_CommonCuts','NCK_TailCuts','NCK_Audit']
for i,m in enumerate(modules,37):
 a=f'NCK_L{i:03}'
 assert not (E/a/'receipt.json').exists()
 r=subprocess.run(['python3',str(E/'NCK_build.py'),a,str(R/'lean'/(m+'.lean')),m],capture_output=True,text=True)
 (E/(a+'-driver.log')).write_text(r.stdout+r.stderr)
 print(a,m,r.stdout[:500],flush=True)
 if r.returncode!=0:raise SystemExit('STOP wrapper error '+r.stderr)
 rc=json.loads((E/a/'receipt.json').read_text())
 if rc['exit_status']!=0:raise SystemExit('STOP changed module failed; inspect before dependent build')
