from pathlib import Path
import sys,subprocess
E=Path(__file__).resolve().parent
plan=[('NLC_L019','NLC_Progress'),('NLC_L092','NLC_SourceInvocation'),('NLC_L093','NLC_Suboccurrences'),('NLC_L094','NLC_ReadyBase'),('NLC_L095','NLC_Ready0'),('NLC_L096','NLC_Ready1'),('NLC_L097','NLC_Ready2'),('NLC_L098','NLC_Ready3'),('NLC_L099','NLC_Ready')]
for a,mod in plan:
 subprocess.run([sys.executable,str(E/'NLC_config.py'),a,mod],check=True)
 r=subprocess.run([sys.executable,str(E/'NLC_run.py'),a])
 if r.returncode:sys.exit(r.returncode)
