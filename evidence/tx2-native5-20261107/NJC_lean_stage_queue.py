from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for a,m in [('NJC_L059','NJC_RawWindows'),('NJC_L060','NJC_OrderedCalls'),('NJC_L061','NJC_OptionClause'),('NJC_L062','NJC_ValidateResult')]:
 r=subprocess.run(['python3',str(E/'NJC_run.py'),a,'lean',m]);assert r.returncode==0,(a,r.returncode)
