"""Reconstruct large source-map inputs from this checkout (not a Lean launch).
The committed pins identify the particular inputs used for this audit.
"""
from pathlib import Path
import hashlib,json
E=Path(__file__).resolve().parent;R=E.parents[1];sources={}
for base in ['docs/research/100bit-spend-path-20261013/lean','lean']:
 for p in (R/base).glob('*.lean'):
  sources[p.stem]=dict(path=str(p.relative_to(R)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),text=p.read_text())
(E/'TAu_repo.json').write_text(json.dumps(sources))
(E/'TAu_base.json').write_bytes((R/'evidence/finish-global-20261026/FGl_019/receipt.json').read_bytes())
print('Source map only. Do not launch unchanged historical attempts; audit budget exhausted.')
