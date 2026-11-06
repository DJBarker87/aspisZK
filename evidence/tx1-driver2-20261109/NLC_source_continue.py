from pathlib import Path
import sys,subprocess
E=Path(__file__).resolve().parent
mods=['NLC_LeafSound','NLC_RankBase','NLC_Rank0','NLC_Rank1','NLC_Rank2','NLC_Rank3','NLC_Rank','NLC_Progress','NLC_SourceInvocation','NLC_Suboccurrences','NLC_ReadyBase','NLC_Ready0','NLC_Ready1','NLC_Ready2','NLC_Ready3','NLC_Ready']
for idx,mod in enumerate(mods,84):
 a=f'NLC_L{idx:03}'
 subprocess.run([sys.executable,str(E/'NLC_config.py'),a,mod],check=True)
 r=subprocess.run([sys.executable,str(E/'NLC_run.py'),a])
 if r.returncode:sys.exit(r.returncode)
