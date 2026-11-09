#!/usr/bin/env python3
"""Builds PCQE_COVERAGE.json and PCQE_HAND_MODELS.json from the PCQE receipts/emissions and the MISSING entries of
PCQC_COVERAGE.json (the P1c failures this phase retries). Name-level presence only; equality is P2/P3."""
import json,re,sys
from pathlib import Path
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;EV=E.parent
J=lambda p:json.loads(Path(p).read_text())
old=J(EV/'prov-p1c-20261109/PCQC_COVERAGE.json')
SPECS={'S004':['E001'],'S005':['E002'],'S016':['E003'],'S022':['E004'],'S019':['E005'],'S010':['E006','E010','E011'],'S1V':['E007'],'S012':['E008','E009']}
DEF=re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(def|structure|inductive|axiom|opaque|abbrev|theorem)\s+([^\s:(\[{]+)",re.M)
runs={}
for n in sorted(set(x for v in SPECS.values() for x in v)):
    run='PCQE_'+n;sp=J(E/(run+'_spec.json'));rc=E/run/'receipt.json'
    ex=J(rc)['exit_status'] if rc.exists() else None
    d=E/(run+'_emitted/raw')
    defs={}
    if ex==0 and d.exists():
        for f in sorted(d.glob('*/*.lean')):
            for k,nm in DEF.findall(f.read_text()):
                defs.setdefault(nm,[]).append(dict(file=str(f.relative_to(EV)),kind=k,external='External' in f.name))
    runs[run]=dict(exit=ex,spec=sp,defs=defs,dir=str(d.relative_to(EV))+'/'+sp['configuration']['namespace'],roots=sp['configuration']['start_from'])
def norm(g):
    p=g.split('.')[1:]
    if p and p[0] in('aspis_core','aspis_statement'):p=p[1:]
    return '.'.join(p)
cov=dict(schema=1,target_established=False,
 note='P1d: retries of P1c-failed selections with the rebuilt ORIGINAL Aeneas b59d5188 (sha256 959659a6...) and original Charon daad69be (driver efdbe5b8); overflow checks ON as in P1c. Name-level presence only; equality is P2/P3. Emissions listed here come from the ORIGINAL Aeneas, a different tool from the b59d5188-extended build behind the other fresh emissions; P2 must use the gate-compatible library for them. Only definitions MISSING in PCQC_COVERAGE.json are tabled.',specs={})
p2={}
for sid,ns in SPECS.items():
    o=old['specs'][sid];miss=[g for g,x in o['definitions'].items() if x['status']=='MISSING']
    good=[n for n in ns if runs['PCQE_'+n]['exit']==0]
    e=dict(attempts=[dict(run='PCQE_'+n,exit=runs['PCQE_'+n]['exit'],roots=runs['PCQE_'+n]['roots'],aeneas='original 959659a6') for n in ns],
      successful_runs=['PCQE_'+n for n in good],modules=o['modules'],overflow_checks_runs=['PCQE_'+n for n in good],definitions={})
    for g in miss:
        n=norm(g);short=n.split('.')[-1];hit=None
        for r in good:
            D=runs['PCQE_'+r]['defs']
            cands=[k for k in D if k==n or k.endswith('.'+n) or k.endswith('.'+short) and n.split('.')[-2:]==k.split('.')[-2:] ]
            if cands:hit=(r,cands[0],D[cands[0]]);break
        if hit:
            body=[h for h in hit[2] if h['kind'] not in('axiom','opaque')]
            e['definitions'][g]=dict(status='FRESH_PRESENT' if body else 'FRESH_EXTERNAL_AXIOM_ONLY',fresh=hit[1],run='PCQE_'+hit[0],via='own',tool='original Aeneas 959659a6',where=hit[2])
            dd=runs['PCQE_'+hit[0]]['dir']
            for m in o['modules']:
                p2.setdefault(m,{}).setdefault(dd,dict(run='PCQE_'+hit[0],dir=dd,tool='original Aeneas 959659a6',definitions=[]))['definitions'].append(g)
        else:
            e['definitions'][g]=dict(status='MISSING',reason=('no fresh definition named %s in %s'%(n,['PCQE_'+x for x in good])) if good else 'no successful P1d extraction (see PCQE_FAILURES.json)')
    cov['specs'][sid]=e
cov['p2_emission_dirs_per_gate_module']={m:sorted(v.values(),key=lambda x:x['run']) for m,v in sorted(p2.items())}
c={}
for e in cov['specs'].values():
    for d in e['definitions'].values():c[d['status']]=c.get(d['status'],0)+1
cov['summary']=c
(E/'PCQE_COVERAGE.json').write_text(json.dumps(cov,indent=1)+'\n');print(c)
for sid,e in cov['specs'].items():
    print(sid,[a['exit'] for a in e['attempts']],{g.split('.')[-1]:d['status'][:7] for g,d in e['definitions'].items()})
# hand models: external (axiom/opaque) names in each successful emission, record only
hm={}
for r,v in runs.items():
    if v['exit']!=0:continue
    hm[r]=sorted(k for k,w in v['defs'].items() if all(h['kind'] in('axiom','opaque') for h in w))
(E/'PCQE_HAND_MODELS.json').write_text(json.dumps(dict(note='Record only; no trust row proposed. Names defined only as axiom/opaque (External files) in each P1d emission; a gate hand model for these is not replaced by this phase.',runs=hm),indent=1)+'\n')
