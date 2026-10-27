"""Preserve exact harness inputs as patches, without committing Rust source trees."""
from pathlib import Path
import difflib,json,hashlib
B=Path('/home/dombarker/project-offloads/codex-cx-leaf-p6-3-20261027')
A=Path('/home/dombarker/project-offloads/codex-cx-leaf-p6-1-20261027/LPa_src')
D=B/'LPc_INPUTS';D.mkdir(exist_ok=True);rows={}
for p in sorted(B.glob('LPc_K*/receipt.json')):
 r=json.loads(p.read_text());out=''
 for f in r['sources']:
  if not f.endswith('.rs'):continue
  src=p.parent/'sources'/f;rel=f.removeprefix('LPc_src/');base=A/rel
  before=base.read_text() if base.exists() else '';after=src.read_text()
  if before==after:continue
  out+=''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='a/'+rel if base.exists() else '/dev/null',tofile='b/'+rel))
 h=hashlib.sha256(out.encode()).hexdigest();(D/(h+'.patch')).write_text(out)
 rows[r['attempt']]={'patch':h+'.patch','sha256':h,'bytes':len(out.encode()),'source_hashes':r['source_hashes']}
(D/'LPc_input-map.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps({'attempts':len(rows),'unique_patches':len(list(D.glob('*.patch')))}))
