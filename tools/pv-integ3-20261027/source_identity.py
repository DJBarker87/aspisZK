from pathlib import Path
import subprocess,json,hashlib
E=Path('evidence/pv-integ1-20261027/d298');D='/home/dombarker/project-offloads/codex-pv-integ1-20261027/d298';H='dombarker@100.108.41.90'
code="""from pathlib import Path
import hashlib,json
D=Path(%r)/'source'
print(json.dumps({str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in D.rglob('*') if p.is_file()}))
"""%D
rows=json.loads(subprocess.run(['ssh',H,'python3','-'],input=code,text=True,capture_output=True,check=True).stdout);bad=[]
# Use git object IDs to compare every exported build input in one batch.
proc=subprocess.Popen(['git','cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
for p,h in rows.items():
 proc.stdin.write(('9ff5a4594e:'+p+'\n').encode());proc.stdin.flush()
 header=proc.stdout.readline().split();assert header[1]==b'blob',(p,header)
 data=proc.stdout.read(int(header[2]));assert proc.stdout.read(1)==b'\n'
 if hashlib.sha256(data).hexdigest()!=h:bad.append(p)
proc.stdin.close();proc.wait()
report=dict(revision=subprocess.check_output(['git','rev-parse','9ff5a4594e'],text=True).strip(),files=rows,disagreements=bad,passed=not bad)
(E/'source-identity.json').write_text(json.dumps(report,indent=2)+'\n');print(len(rows),'files; disagreements:',bad)
assert not bad
