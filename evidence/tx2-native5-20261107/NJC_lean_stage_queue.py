from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for a,m in [('NJC_L087','NJC_RawCalls'),('NJC_L088','NJC_ResumeCalls'),('NJC_L089','NJC_OrderedCalls')]:
 r=subprocess.run(['python3',str(E/'NJC_run.py'),a,'lean',m]);assert r.returncode==0,(a,r.returncode)
