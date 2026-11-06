"""Read-only receipt recovery, never submit a prover."""
from pathlib import Path
import subprocess,json,sys,base64,hashlib,lzma
E=Path(__file__).resolve().parent;a=sys.argv[1];B='/home/dombarker/project-offloads/codex-cx-batch-merkle2-20261108'
code=f'''from pathlib import Path
import base64,json
b=Path({B!r});paths=list((b/{a!r}).rglob('*'))+list((b/{(a+'_validation')!r}).rglob('*'))
print(json.dumps({{str(p.relative_to(b)):base64.b64encode(p.read_bytes()).decode() for p in paths if p.is_file()}}))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
for n,t in json.loads(r.stdout).items():
 p=E/n;p.parent.mkdir(parents=True,exist_ok=True);raw=base64.b64decode(t)
 if len(raw)>1000000 and not n.endswith('.xz'):
  p.with_name(p.name+'.xz').write_bytes(lzma.compress(raw,preset=6));p.with_name(p.name+'.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
 else:p.write_bytes(raw)
x=json.loads((E/a/'receipt.json').read_text());entries=[json.loads(t) for t in (E/'NKB_ATTEMPTS.jsonl').read_text().splitlines()]
if not any(t['attempt']==a for t in entries):
 entry={k:v for k,v in x.items() if k not in ['deps_fingerprint','env']};entry['full_receipt']=a+'/receipt.json'
 with (E/'NKB_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(entry)+'\n')
print(a,'recovered read-only exit',x['exit_status'])
