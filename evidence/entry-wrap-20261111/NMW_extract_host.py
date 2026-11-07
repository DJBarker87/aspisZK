"""Apply owner Pool pin in own scratch, then fresh process-only extraction."""
from pathlib import Path
import base64,hashlib,json,lzma,subprocess
B=Path(__file__).resolve().parent
m=json.loads((B/'NMW_POOL_AMENDMENT.json').read_text())
payload=json.loads(lzma.decompress((B/'NMW_FROZEN_PAYLOAD.json.xz').read_bytes()))
for row in m['changes']:
 p=B/'NMW_src'/row['path']
 assert p.resolve().is_relative_to((B/'NMW_src/programs/aspis-pool').resolve())
 assert hashlib.sha256(p.read_bytes()).hexdigest()==row['old_sha256'],str(p)
 if row['new_sha256'] is None:p.unlink()
 else:
  data=base64.b64decode(payload[row['path']]);assert hashlib.sha256(data).hexdigest()==row['new_sha256'];p.write_bytes(data)
r=subprocess.run(['python3',str(B/'NMW_stage.py'),'--extract','--function','process','--workspace',str(B/'NMW_src'),'--out',str(B/'NMW_process_emitted'),'--opacity',str(B/'NMW_OPACITY.json')])
raise SystemExit(r.returncode)
