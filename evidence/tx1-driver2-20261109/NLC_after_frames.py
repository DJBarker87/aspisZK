from pathlib import Path
import sys,subprocess
E=Path(__file__).resolve().parent
r=subprocess.run([sys.executable,str(E/'NLC_native_continue.py')])
if r.returncode:sys.exit(r.returncode)
mods=['NLC_LeafSound','NLC_RankBase','NLC_Rank0','NLC_Rank1','NLC_Rank2','NLC_Rank3','NLC_Rank','NLC_Progress','NLC_SourceInvocation']
for idx,mod in enumerate(mods,84):
 a=f'NLC_L{idx:03}'
 subprocess.run([sys.executable,str(E/'NLC_config.py'),a,mod],check=True)
 r=subprocess.run([sys.executable,str(E/'NLC_run.py'),a])
 if r.returncode:sys.exit(r.returncode)
