from pathlib import Path
import re,json,hashlib,subprocess
root=Path(__file__).resolve().parents[2]; out=Path(__file__).resolve().parent
rows=[]
for prefix in ['crates','docs/research/v8-r0-zk-20261009/z4','docs/research/v8-r0-zk-20261009/c3']:
 for p in sorted((root/prefix).rglob('*.rs')):
  text=p.read_text(); lines=text.splitlines(); fn=''; test=False
  for n,l in enumerate(lines,1):
   f=re.search(r'\bfn\s+(\w+)',l)
   if f:fn=f[1]
   if re.search(r'\b(?:try_inv|inv|inv_with|inv_r|inverse_raw|invm|inverse|invert|m31_batch_inverse|cm31_batch_inverse)(?:_with)?\s*\(',l):
    rows.append(dict(path=str(p.relative_to(root)),line=n,function=fn,source=l.strip(),file_sha256=hashlib.sha256(text.encode()).hexdigest(),classification='candidate; resolve with INVENTORY.md'))
(out/'candidates.json').write_text(json.dumps(rows,indent=2)+'\n')
# The baseline revision file is immutable after the stage-1 pin.
print(len(rows),'candidate source lines')
