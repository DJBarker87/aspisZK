#!/usr/bin/env python3
"""PCUA_survey.py: for each hub-cluster gate module, list which fresh frozen emission directories contain the Rust item
of each reached definition (match by Aeneas doc-comment path with the crate name normalized). Record only."""
import json,re,sys
from pathlib import Path
sys.dont_write_bytecode=True
EV=Path(__file__).resolve().parent.parent
P=json.loads((EV/'prov-p0-20261109/PCO_PARTITION.json').read_text())
MODS=sys.argv[1:]
items={}
for f in sorted(EV.rglob('raw/*/Funs.lean'))+sorted(EV.rglob('raw/*/Types.lean')):
    d=f.parent; txt=f.read_text()
    for m in re.finditer(r'/-- (?:Trait implementation: )?\[([A-Za-z0-9_]+)::(.*?)\](?::|\s*\n)',txt):
        rp=m.group(2)
        rp=re.sub(r'\b'+re.escape(m.group(1))+r'::','',rp) # drop crate prefix
        rp=re.sub(r'\{[^{}]*\bfor\b','{impl for',rp) if False else rp
        items.setdefault(rp,set()).add(str(d.relative_to(EV))+'/'+f.name)
def norm(r):
    r=r.replace('CRATE::','')
    return r
out={}
for M in MODS:
    mod=P['modules'][M]; res={}
    for dn,info in mod['reached_definitions'].items():
        r=norm(info['rust'])
        res[dn]=dict(rust=info['rust'],coverage=info['coverage'],fresh=sorted(items.get(r,[])))
    out[M]=res
print(json.dumps(out,indent=1))
