from pathlib import Path
import json,hashlib,difflib
B=Path(__file__).resolve().parent;S=B/'NLU_src';p=S/'programs/r1-cost-probe/src/NLU_program.rs';before=p.read_text();after=(B/'NLU_program.rs.txt').read_text();p.write_text(after)
pins=json.loads((B/'NLU_SOURCE_PINS.json').read_text());pins[str(p.relative_to(S))]=hashlib.sha256(p.read_bytes()).hexdigest();(B/'NLU_SOURCE_PINS.json').write_text(json.dumps(pins))
with (B/'NLU_NATIVE.patch').open('a') as f:f.write(''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='a/'+str(p.relative_to(S)),tofile='b/'+str(p.relative_to(S)))))
print('Updated own harness inputs; frozen production bytes untouched')
