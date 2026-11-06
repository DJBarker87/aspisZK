from pathlib import Path
import subprocess,json,sys
B=Path.cwd();groups=json.loads((B/'NIX_AUDIT_ROOTS.json').read_text())['groups']
for i in range(len(groups)):
 r=subprocess.run(['python3','NIX_batch.py','batch'+str(i)])
 if r.returncode:sys.exit(r.returncode)
print(json.dumps(dict(groups=len(groups),roots=sum(map(len,groups)),status='PASS_ALL_NEW_ROOTS_AND_HEADLINE')))
