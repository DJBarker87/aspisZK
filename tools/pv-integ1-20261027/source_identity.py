from pathlib import Path
import subprocess,json,hashlib
E=Path('evidence/pv-integ1-20261027');D='/home/dombarker/project-offloads/codex-pv-integ1-20261027';H='dombarker@100.108.41.90'
code='''from pathlib import Path
import hashlib,json
D=Path(DIR)/'source'
print(json.dumps({str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in D.rglob('*') if p.is_file() and 'target' not in p.relative_to(D).parts}))
'''.replace('DIR',repr(D))
rows=json.loads(subprocess.run(['ssh',H,'python3','-'],input=code,text=True,capture_output=True,check=True).stdout);bad=[]
for p,h in rows.items():
 r=subprocess.run(['git','show','0c9dc9a4cc:'+p],capture_output=True)
 if r.returncode or hashlib.sha256(r.stdout).hexdigest()!=h:bad.append(p)
report=dict(revision=subprocess.check_output(['git','rev-parse','0c9dc9a4cc'],text=True).strip(),files=rows,disagreements=bad,passed=not bad)
(E/'source-identity.json').write_text(json.dumps(report,indent=2)+'\n');print(len(rows),'files; disagreements:',bad)
