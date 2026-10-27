"""Archive one harness's real Kani metadata and retained GOTO hashes, read-only."""
from pathlib import Path
import json,subprocess,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin12-20261027';number=int(sys.argv[1]);inv=[json.loads(x) for x in (E/'kani-invocations.jsonl').read_text().splitlines()];row=next(x for x in inv if x['number']==number)
code='''from pathlib import Path
import json,hashlib
p=Path('/home/dombarker/project-offloads/codex-pv-runjoin-20261026/target/kani/x86_64-unknown-linux-gnu/debug/deps')
found=[]
for f in p.glob('*kani-metadata.json'):
 x=json.loads(f.read_text())
 for h in x.get('proof_harnesses',[]):
  if h.get('pretty_name')==HARNESS:
   q=Path(h['goto_file']);paths=[f,q,Path(str(q).replace('.symtab.out','.out'))]
   found.append(dict(metadata=h,files={str(v):dict(sha256=hashlib.sha256(v.read_bytes()).hexdigest(),size=v.stat().st_size) for v in paths if v.exists()}))
print(json.dumps(found))
'''.replace('HARNESS',repr(row['harness']))
p=subprocess.run(['ssh','-o','BatchMode=yes','dombarker@100.108.41.90','python3','-c',__import__('shlex').quote(code)],capture_output=True,text=True,check=True)
found=json.loads(p.stdout);assert found
for x in found:
 assert x['metadata']['attributes']['stubs']==[]
 assert x['metadata']['attributes']['verified_stubs']==[]
 assert not x['metadata']['has_loop_contracts']
(E/f'kani-metadata-{number:02d}.json').write_text(json.dumps(dict(number=number,invocation=row,records=found,classification='real metadata and model hashes; inspection does not establish verification'),indent=2)+'\n')
print('archived real unstubbed metadata',number)
