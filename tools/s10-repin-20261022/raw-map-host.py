#!/usr/bin/env python3
"""Give each newly emitted ELF symbol its own identity, never an old address."""
import hashlib,json
from pathlib import Path
H=Path('/home/dombarker/project-offloads/codex-cx-s10-repin-20261022')
x=json.loads((H/'collected/elf-graphs.json').read_text())
k=json.loads((H/'collected/elf-symbol-kinds.json').read_text())
rows=[]
for mode,g in x['artifacts'].items():
 for s in g['symbols']:
  aliases=[r['raw_name'] for r in k['artifacts'][mode]['symbols'] if r['address']==s['address'] and r['size']==s['size']]
  assert aliases
  if not s['size']:continue
  rows.append(dict(artifact=mode,id=f"elf:{mode}:{s['address']:x}:"+hashlib.sha256(s['name'].encode()).hexdigest()[:16],raw_symbol_aliases=aliases,**s))
(H/'elf-raw-input.json').write_text(json.dumps(rows,indent=2,sort_keys=True)+'\n')
print(dict(records=len(rows)))
