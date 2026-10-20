import hashlib,json,sys
from pathlib import Path
H=Path(sys.argv[1]);rows=[]
for p in sorted((H/'artifacts').rglob('*')):
 if p.is_file() and (p.suffix in ['.so','.elf'] or p.name in ['pool_gate','pool_gate_trace']):
  rows.append(dict(path=str(p.relative_to(H)),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
(H/'artifacts.json').write_text(json.dumps(rows,indent=1)+'\n')
(H/'artifacts-sha256.txt').write_text(''.join(f"{r['sha256']}  {r['bytes']} bytes  {r['path']}\n" for r in rows))
print(len(rows),'binary hashes, no exported binaries')
