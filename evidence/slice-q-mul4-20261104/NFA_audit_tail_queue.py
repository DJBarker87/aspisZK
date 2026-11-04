from pathlib import Path
import json,subprocess,os
E=Path(__file__).resolve().parent
entries=json.loads((E/'NFA_AUDIT_ROOTS.json').read_text())
for i in range(44,len(entries)):
 a='NFA_L'+str(i+4).zfill(3)
 r=subprocess.run(['python3',str(E/'NFA_run.py'),a,'audit',str(i)],env={**os.environ,'NFA_SINT2_FIRST':'1'},stdout=(E/(a+'-client.log')).open('w'),stderr=subprocess.STDOUT)
 print(a,entries[i]['module'],'exit',r.returncode,flush=True)
 if r.returncode:break
