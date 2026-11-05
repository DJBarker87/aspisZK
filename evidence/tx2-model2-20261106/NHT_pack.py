"""Keep repeated large pinned inputs once, with hash-checked source references."""
from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
refs=json.loads((E/'NHT_PACK.json').read_text()) if (E/'NHT_PACK.json').exists() else {}
for p in E.glob('NHT_L???/sources/NHT_EXPECTED_IMPORTS.jsonl'):
 q=E/'NHT_EXPECTED_IMPORTS.jsonl';assert sha(p)==sha(q)
 refs[str(p.relative_to(E))]=dict(canonical=str(q.relative_to(E)),sha256=sha(q),bytes=p.stat().st_size)
 p.unlink()
(E/'NHT_PACK.json').write_text(json.dumps(refs,indent=1)+'\n')
print(json.dumps(dict(packed=len(refs),deduplicated_bytes=sum(x['bytes'] for x in refs.values()))))
