from pathlib import Path
import json,hashlib,difflib
B=Path(__file__).resolve().parent;S=B/'NKA_src';pins=json.loads((B/'NKA_SOURCE_PINS.json').read_text());frozen=json.loads((B/'NKA_FROZEN_FILE_PINS.json').read_text());n='crates/aspis-r1-cost-probe/src/r1_semantic.rs';p=S/n;assert hashlib.sha256(p.read_bytes()).hexdigest()==frozen[n];old=p.read_text();p.write_text(old+'\n'+(B/'NKA_claims_cleanup.rs.txt').read_text());pins[n]=hashlib.sha256(p.read_bytes()).hexdigest();del frozen[n]
(B/'NKA_SOURCE_PINS.json').write_text(json.dumps(pins,indent=2));(B/'NKA_FROZEN_FILE_PINS.json').write_text(json.dumps(frozen,indent=2));(B/'NKA_CLAIMS_CLEANUP.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),p.read_text().splitlines(True),fromfile='a/'+n,tofile='b/'+n)))
print('NKA actual-typed claims rejection cleanup stage installed')
