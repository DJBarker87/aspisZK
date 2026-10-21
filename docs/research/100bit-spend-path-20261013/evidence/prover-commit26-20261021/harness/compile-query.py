from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent.parent
rows=json.loads((E/'query-owners.json').read_text())
start=int(sys.argv[1]); stop=int(sys.argv[2]); attempt=int(sys.argv[3])
for row in rows[start:stop]:
 print('ATTEMPT',attempt,row['module'],flush=True)
 subprocess.run(['python3',str(E/'harness/lean.py'),row['module'],str(attempt),'--wait'],check=True)
 attempt+=1
