#!/usr/bin/env python3
"""PCQ_A_COVERAGE.json: map each committed gate definition named in a P1a spec's covers.definitions to the fresh
emission definition (per successful run) that covers it, or MISSING with reason. Name rule: strip the gate module
namespace (first dotted segment) and an optional leading crate segment (aspis_core / aspis_statement); compare with
the fresh Aeneas name (namespace PCQ_* removed). Mapping is by NAME only: it asserts presence in a fresh emission,
not equality (equality is P2)."""
import json,re,sys,glob
from pathlib import Path
E=Path(__file__).resolve().parent
DEF=re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(def|structure|inductive|axiom|opaque|abbrev|theorem)\s+([^\s:(\[{]+)",re.M)
def fresh_defs(run):
    out={}
    for f in sorted((E/(run+'_emitted/raw')).glob('*/*.lean')):
        txt=f.read_text()
        for kind,name in DEF.findall(txt):
            out.setdefault(name,[]).append(dict(file=str(f.relative_to(E)),kind=kind,external='External' in f.name))
    return out
def norm(g):
    parts=g.split('.')[1:]
    if parts and parts[0] in('aspis_core','aspis_statement'):parts=parts[1:]
    return '.'.join(parts)
res={'superseded_runs':None,'schema':1,'target_established':False,'note':'name-level presence only; equality is P2','specs':{}}
specs={s['spec_id']:s for s in json.loads((E/'PCQ_extract_specs.json').read_text())['specs']}
allruns=[]
for f in sorted(E.glob('PCQ_E[0-9][0-9][0-9]_spec.json')):
    s=json.loads(f.read_text());run=s['run']
    rc=(E/run/'receipt.json')
    ex=json.loads(rc.read_text())['exit_status'] if rc.exists() else None
    allruns.append(dict(ovf=bool(s.get('extra_env')),run=run,spec_id=s['spec_id'],crate=s['configuration']['crate'],ns=s['configuration']['namespace'],exit=ex))
SUPERSEDED={'PCQ_E004':'wrong manifest shape (cost-probe crate, aspis_statement:: roots): exit 0 but empty Funs.lean; superseded by PCQ_E014/E018','PCQ_E007':'same wrong shape as E004: exit 0, empty Funs.lean; superseded by PCQ_E026'}
good=[r for r in allruns if r['run'] not in SUPERSEDED and r['exit']==0 and (E/(r['run']+'_emitted/raw')).exists()]
TYPES_ONLY={'S003','S007','S008'}  # original frozen_types_only selections: roots derived from callers, covered by name in sibling runs of the same crate
for sid,sp in sorted(specs.items()):
    if sp.get('p1_half')!='P1a' or sp.get('pilot') or re.search(r'[a-z]$',sid):continue
    own=[r for r in allruns if r['spec_id']==sid or (re.fullmatch(sid+'[a-z]',r['spec_id']))]
    cand=[r for r in good if r in own] or ([r for r in good if r['crate']==sp['crate']] if sid in TYPES_ONLY else [])
    entry=dict(attempts=[dict(run=r['run'],spec=r['spec_id'],exit=r['exit']) for r in own],successful_runs=[r['run'] for r in cand],definitions={},modules=sp['covers']['modules'])
    cand=sorted(cand,key=lambda r:not r['ovf'])
    entry['overflow_checks_runs']=[r['run'] for r in cand if r['ovf']];entry['runs_without_overflow_checks']=[r['run'] for r in cand if not r['ovf']]
    fds={r['run']:fresh_defs(r['run']) for r in cand}
    for g in sp['covers']['definitions']:
        n=norm(g);hits=[(run,fd[n]) for run,fd in fds.items() if n in fd]
        if hits:
            body=[h for run_,hs in hits for h in hs if h['kind'] not in('axiom','opaque')]
            entry['definitions'][g]=dict(status='FRESH_PRESENT' if body else 'FRESH_EXTERNAL_AXIOM_ONLY',fresh=n,run=hits[0][0],where=hits[0][1])
        else:entry['definitions'][g]=dict(status='MISSING',reason=('no fresh definition named %s in %s'%(n,[r['run'] for r in cand])) if cand else 'no successful extraction (see PCQ_A_FAILURES.json)')
    res['specs'][sid]=entry
res['superseded_runs']=SUPERSEDED
(E/'PCQ_A_COVERAGE.json').write_text(json.dumps(res,indent=1)+'\n')
c={}
for e in res['specs'].values():
    for d in e['definitions'].values():c[d['status']]=c.get(d['status'],0)+1
print(c)
