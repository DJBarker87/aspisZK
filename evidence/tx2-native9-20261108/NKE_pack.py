"""Losslessly retain historical source inputs once by sha256; no input exclusion."""
from pathlib import Path
import json,lzma,hashlib
E=Path(__file__).resolve().parent
p=E/'NKE_INPUT_INDEX.json';index=json.loads(p.read_text()) if p.exists() else {}
completed=[json.loads(line)['attempt'] for line in (E/'NKE_ATTEMPTS.jsonl').read_text().splitlines()]
sources=[src for a in completed for src in sorted((E/a/'sources').rglob('*')) if src.is_file()]
sources += [E/n for n in ['NKE_NATIVE_INPUTS.json','NKE_EXPECTED_IMPORTS.jsonl','NKE_BASE_EXPECTED_IMPORTS.jsonl'] if (E/n).is_file()]
for src in sources:
 raw=src.read_bytes();h=hashlib.sha256(raw).hexdigest();target=E/'NKE_inputs'/(h+'.xz');target.parent.mkdir(exist_ok=True)
 if not target.exists():target.write_bytes(lzma.compress(raw,preset=6))
 assert lzma.decompress(target.read_bytes())==raw
 index[str(src.relative_to(E))]={'retained':str(target.relative_to(E)),'compressed':True,'sha256':h,'bytes':len(raw)}
 src.unlink()
p.write_text(json.dumps(index,indent=2)+'\n')
print(json.dumps({'logical_inputs':len(index),'retained_capsules':len(list((E/'NKE_inputs').glob('*.xz')))}))
