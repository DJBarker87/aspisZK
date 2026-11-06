from pathlib import Path
import json,lzma,base64,hashlib,subprocess
B=Path(__file__).resolve().parent;S=B/'NJG_src';pins=json.loads((B/'NJG_SOURCE_PINS.json').read_text());manifest=json.loads((B/'NHR_STAGING_MANIFEST.json').read_text());payload=json.loads(lzma.decompress((B/'NHR_FROZEN_PAYLOAD.json.xz').read_bytes()));saved={}
for n,h in pins.items():
 p=S/n;assert hashlib.sha256(p.read_bytes()).hexdigest()==h,(n,'scratch guard');saved[n]=p.read_bytes()
(B/'NJG_EXTRACTION_RESTORE.json').write_text(json.dumps({n:base64.b64encode(b).decode() for n,b in saved.items()}))
try:
 for n in saved:
  b=base64.b64decode(payload[n]);assert hashlib.sha256(b).hexdigest()==manifest['files'][n]['sha256'];(S/n).write_bytes(b)
 r=subprocess.run(['python3','NJG_stage.py','--extract','--function','verify_finish','--workspace','NJG_src','--opacity','NJG_OPACITY.json','--out','NJG_emitted/verify_finish'],cwd=B)
finally:
 for n,b in saved.items():(S/n).write_bytes(b)
 restored=all(hashlib.sha256((S/n).read_bytes()).hexdigest()==h for n,h in pins.items());(B/'NJG_EXTRACTION_RESTORED.json').write_text(json.dumps(dict(restored=restored,cargo_target_dir=str(B/'NHR_target'),frozen_revision=manifest['revision'])));assert restored
print('NJG finish extraction exit',r.returncode);raise SystemExit(r.returncode)
