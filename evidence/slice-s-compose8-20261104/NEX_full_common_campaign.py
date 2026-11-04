from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for args in [['97','common','0'],['102','common',','.join(str(i) for i in range(1,15)),'positive,value']]:
 subprocess.run([sys.executable,str(E/'NEX_campaign.py'),*args],check=True)
