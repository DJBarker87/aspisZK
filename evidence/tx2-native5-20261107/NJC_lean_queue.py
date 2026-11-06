from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for a,module in [('NJC_L014','NJC_EReaderResults'),('NJC_L015','NJC_ReaderWindows'),('NJC_L016','NJC_CutTypes'),('NJC_L017','NJC_ResumeCalls'),('NJC_L018','NJC_Sections'),('NJC_L019','NJC_QueryOccurrence')]:
 r=subprocess.run(['python3',str(E/'NJC_run.py'),a,'lean',module]);assert r.returncode==0,(a,module)
 print(a+' passed '+module,flush=True)
