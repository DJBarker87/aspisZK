from NMX_transport import *
r=ssh('python3',f'''from pathlib import Path
import json,hashlib
b=Path({B!r});names=['NMX_generated/NMX_Program.lean','NMX_objects/NMX_Program.olean','NMX_L008/receipt.json','NMX_L009/receipt.json']
rows=[]
for n in names:
 p=b/n;rows.append(dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
for p in (b/'NMX_exports_20261111').glob('*'):
 if p.is_file():rows.append(dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
print(json.dumps(dict(files=rows,generated_program_sha256=hashlib.sha256((b/'NMX_generated/NMX_Program.lean').read_bytes()).hexdigest(),L008=json.loads((b/'NMX_L008/receipt.json').read_text())['source_hashes'],L009=json.loads((b/'NMX_L009/receipt.json').read_text())['source_hashes'],export_complete=False)))
''');assert r.returncode==0,r.stderr
(E/'NMX_RETENTION_RECOVERY.json').write_text(r.stdout)
