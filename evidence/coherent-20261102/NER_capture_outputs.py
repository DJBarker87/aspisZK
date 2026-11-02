"""Pin task-owned rebuilt objects; no authoritative cache modifications."""
from pathlib import Path
import json,hashlib
B=Path(__file__).resolve().parent
modules=['JFw_Validator','JFw_Chunks','JFw_BlockValidation','JFw_Record','JGx_SdkAfterValidationEq']
rows=[]
for mod in modules:
 p=B/(mod+'.olean');s=B/(mod+'.lean')
 rows.append(dict(module=mod,path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size,source_sha256=hashlib.sha256(s.read_bytes()).hexdigest()))
(B/'NER_REBUILT_OBJECT_PINS.json').write_text(json.dumps(rows,indent=2)+'\n')
