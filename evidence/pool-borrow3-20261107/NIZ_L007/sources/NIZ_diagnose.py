from pathlib import Path
import subprocess,hashlib,json
B=Path(__file__).resolve().parent
artifacts=[p for p in (B/'NIZ_target').rglob('*') if p.is_file() and p.suffix in ['.out','.symtab','.json'] and ('kani' in p.name or p.suffix=='.out')]
tools=[p for p in Path('/home/dombarker/.kani').rglob('cbmc') if p.is_file()]
result=dict(artifacts=[dict(path=str(p),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in artifacts],tools=[dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in tools],loops=[])
for p in artifacts:
 if p.suffix!='.out':continue
 command=[str(tools[0]),str(p),'--show-loops']
 r=subprocess.run(command,capture_output=True,text=True,timeout=30)
 result['loops'].append(dict(command=command,exit=r.returncode,stdout=r.stdout,stderr=r.stderr))
print(json.dumps(result))
