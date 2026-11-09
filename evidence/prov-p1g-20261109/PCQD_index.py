#!/usr/bin/env python3
"""PCQD_ coverage index: scan every P1 emission (PCQ/PCQC/PCQE/PCQF/PCQG) and list def-kind names (axioms excluded)."""
import json,re,sys
from pathlib import Path
sys.dont_write_bytecode=True
EV=Path(__file__).resolve().parent.parent
pc=json.loads((EV/'prov-p2f-20261109/PCUF_EMISSION_INDEX.json').read_text())
sup={v['run']:v.get('superseded_by') for v in pc.values()}
TOOL={'PCQ':'aeneas-b59d5188-extended','PCQC':'aeneas-b59d5188-extended','PCQF':'aeneas-b59d5188-extended','PCQE':'aeneas-original-959659a6','PCQG':'aeneas-original-959659a6'}
DECL=re.compile(r'^(?:@\[[^\]]*\]\s*)*(?:noncomputable\s+)?(def|axiom|structure|inductive|opaque|abbrev)\s+(\S+)',re.M)
ENTRY=re.compile(r'^/- \[([^\]]*)\]',re.M)
out={}
for d in sorted(EV.glob('prov-p1[a-g]-*/*_emitted/raw/*')):
    if not d.is_dir():continue
    run=d.parent.parent.name.replace('_emitted','');pfx=run.split('_')[0]
    if pfx not in TOOL:continue
    ns=d.name
    rec={'run':run,'dir':str(d.relative_to(EV)),'tool':TOOL[pfx],'superseded_by':sup.get(run),'defs':{}, 'axioms':[]}
    for f in ('Types.lean','Funs.lean'):
        p=d/f
        if not p.exists():continue
        t=p.read_text()
        for k,n in DECL.findall(t):
            n=n.split('(')[0]
            if k=='axiom':rec['axioms'].append(n)
            else:rec['defs'][n]=k
    pe=d/'FunsExternal_Template.lean'
    if pe.exists():
        for k,n in DECL.findall(pe.read_text()):rec['axioms'].append(n)
    out[str(d.relative_to(EV))]=rec
Path(sys.argv[1] if len(sys.argv)>1 else 'PCQD_INDEX.json').write_text(json.dumps(out,indent=0)+'\n')
print(len(out))
