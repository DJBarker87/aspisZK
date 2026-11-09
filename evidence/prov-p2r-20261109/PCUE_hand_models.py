#!/usr/bin/env python3
"""PCUE_hand_models.py: PCUE_HAND_MODELS.json (record only). For each generated pass: the external names of the fresh overflow-checks-on emission
(axioms of its External templates) that the generated file resolves, by name, to gate constants; the gate text (exact, from the gate source);
the fresh axiom text; and the PROVED definitions of the pass whose fresh body mentions the name (those proofs are conditional on the gate constant)."""
import json,re,sys
from pathlib import Path
sys.dont_write_bytecode=True
import PCUE_gen_equalities as G, PCUE_plan as PL
H=Path(__file__).resolve().parent;EV=H.parent
PLAN=json.load(open(H/'PCUE_PLAN.json'));ST=json.load(open(H/'PCUE_EQ_STATUS.json'))
def label(m,ps): return m.replace('.','_')+ps['tag']
def axiom_text(d,name):
    for f in ('FunsExternal_Template.lean','TypesExternal_Template.lean'):
        p=EV/d/f
        if p.exists():
            m=re.search(r'(?m)^(?:@\[[^\]]*\]\s*)*axiom\s+'+re.escape(name)+r'\b.*?(?=\n\n|\Z)',p.read_text(),re.S)
            if m: return f,m.group(0).strip()[:600]
    return None,None
def crate_of(n):
    if n.startswith('aspis_core.'): return 'aspis-core (workspace member of the frozen tree 4bb3b3f)'
    if n.startswith(('core.','MutAArray','alloc.','Array.','Slice.','Shared')): return 'rust core/alloc/std models of the Aeneas library'
    return 'aspis-r1-cost-probe or aspis-statement (workspace member of the frozen tree 4bb3b3f)'
out=[]
for m,r in PLAN.items():
    if not r['passes']: continue
    g,q,o=PL.gate_sources(m);gb={b['name']:b for b in G.parse_blocks(g) if b['kind']=='decl'}
    if q: gb.update({b['name']:b for b in G.parse_blocks(q) if b['kind']=='decl'})
    for ps in r['passes']:
        lab=label(m,ps);rp=H/f'gen/PRVEq_{lab}.report2.json'
        if not rp.exists(): continue
        rep=json.load(open(rp));ext=sorted(set((rep.get('external_funs') or [])+(rep.get('external_types') or [])))
        fp=EV/ps['fresh_dir']/('Types.lean' if ps['kind']=='Types' else 'Funs.lean')
        fb={b['name']:b for b in G.parse_blocks(fp.read_text()) if b['kind']=='decl'}
        for n in ext:
            if n in fb and 'external' not in str(fb[n].get('dkind')): pass
            dep=[]
            for full,e in ST['modules'][m]['reached'].items():
                fn=e.get('fresh_name')
                if e.get('pass_label')==lab and e['status'].startswith('PROVED') and fn in fb and n in G.lean_ident_tokens(fb[fn]['body']): dep.append(full)
            gate=None
            for v in PL.variants(n):
                if v in gb:
                    t=gb[v]['text'];gate=dict(name=v,aeneas_generated_text=bool(re.search(r'/--\s*(Trait implementation: )?\[[A-Za-z0-9_]+::',t)) and 'Source:' in t,text=t.strip()[:1500]);break
            f,ax=axiom_text(ps['fresh_dir'],n)
            out.append(dict(pass_label=lab,gate_module=m,fresh_dir=ps['fresh_dir'],external_name=n,resolved_to_gate_constant_by_name=n in (rep.get('names_resolved_to_gate_funs') or []),
                            fresh_axiom_file=f,fresh_axiom_text=ax,gate_definition=gate,pinned_crate=crate_of(n),proved_definitions_conditional_on_it=dep or None,
                            note=('no gate definition of this name (or recorded prefix variant) in the gate source; the generated file only elaborates if the compiled gate environment supplies it' if gate is None else 'gate text found; whether it is the intended model of the Rust item is not proved here')))
Path(H/'PCUE_HAND_MODELS.json').write_text(json.dumps(dict(schema='PCUE_HAND_MODELS/1',target_established=False,note='Record only; no trust row added or proposed.',entries=out),indent=1))
print(len(out),'entries;',sum(1 for o in out if o['proved_definitions_conditional_on_it']),'with conditional proved definitions')
