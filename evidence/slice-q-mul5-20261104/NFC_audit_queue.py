from pathlib import Path
import json,subprocess
E=Path(__file__).resolve().parent
entries=json.loads((E/'NFC_PROOF_ROOTS.json').read_text())['groups']
assert len(entries)==38
for i,roots in enumerate(entries):
 a=f'NFC_L{i+63:03}';assert i+63<=100
 r=subprocess.run(['python3',str(E/'NFC_run.py'),a,'auditbin','proof'+str(i)],stdout=(E/(a+'-client.log')).open('w'),stderr=subprocess.STDOUT)
 print(a,'roots',len(roots),'exit',r.returncode,flush=True)
 if r.returncode:break
