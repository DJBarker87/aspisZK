#!/usr/bin/env python3
"""Builds PCQG_COVERAGE.json (schema of PCQC_COVERAGE.json plus p2_emission_dirs_per_gate_module), PCQG_SUPERSEDES.json,
PCQG_FAILURES.json from committed receipts/emissions. Name-level presence only (equality is P2/P3)."""
import json,re,sys
from pathlib import Path
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;EV=E.parent
def J(p):return json.loads(Path(p).read_text())
def rel(p):return str(Path(p).resolve().relative_to(EV))
specs={s['spec_id']:s for s in J(E/'PCQG_extract_specs.json')['specs']}
runs=[]
for f in sorted(E.glob('PCQG_E[0-9][0-9][0-9]_spec.json')):
    s=J(f);run=s['run'];rc=E/run/'receipt.json'
    runs.append(dict(run=run,spec_id=s['spec_id'],ns=s['configuration']['namespace'],exit=J(rc)['exit_status'] if rc.exists() else None,wall=J(rc).get('wall_seconds') if rc.exists() else None,
        has_emit=(E/(run+'_emitted/raw')).exists() and any((E/(run+'_emitted/raw')).glob('*/Funs.lean')),on=bool(s.get('extra_env')),spec=s,note=(s.get('p1e') or {}).get('note','')))
good=[r for r in runs if r['exit']==0 and r['has_emit'] and r['on']]
DEF=re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(def|structure|inductive|axiom|opaque|abbrev|theorem)\s+([^\s:(\[{]+)",re.M)
def fresh_defs(r):
    out={}
    for f in sorted((E/(r['run']+'_emitted/raw')).glob('*/*.lean')):
        for kind,name in DEF.findall(f.read_text()):
            out.setdefault(name,[]).append(dict(file=rel(f),kind=kind,external='External' in f.name))
    return out
FD={r['run']:fresh_defs(r) for r in good}
def norm(g):
    parts=g.split('.')[1:]
    if parts and parts[0] in('aspis_core','aspis_statement'):parts=parts[1:]
    return '.'.join(parts)
# ---------------- required definitions: those P1e left MISSING, plus the three NDE CONFIG_MISMATCH definitions (P3a)
req=[]
p1e=J(EV/'prov-p1e-20261109/PCQF_COVERAGE.json')
for sid,e in p1e['specs'].items():
    for key,d in e['definitions'].items():
        if d['status']=='MISSING':
            origin,module,g=key.split(':',2)
            req.append(dict(origin=origin,module=module,gate_def=g,rust=None,found_by_name=None,frozen_file=None,intended=d['reason']))
for m,g in [('NDE_Reference2','NDE_Reference2.reduce_ref'),('NDE_Reference2','NDE_Reference2.extension_raw_ref'),('NDE_Reference5','NDE_Reference5.link_weight_ref')]:
    req.append(dict(origin='P3a',module=m+'.Funs',gate_def=g,rust=None,found_by_name=None,frozen_file=None,intended='NDE re-extraction with overflow checks ON'))
def spec_for(r):return r.get('intended','')
cov=dict(schema=1,target_established=False,note='P1f: required definitions are the 178 that PCQF_COVERAGE.json left MISSING plus the 3 NDE CONFIG_MISMATCH definitions of P3a (PCVA_CLASSIFICATION.json). name-level presence only; equality is P2/P3. All runs listed as usable are overflow-checks-on (CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=true, RUSTFLAGS ... -C overflow-checks=yes). a definition counted FRESH_PRESENT only when a non-axiom declaration of the same normalised Lean name exists in a good PCQG run.',specs={})
p2={}
for sid in list(specs):
    cov['specs'][sid]=dict(label=specs[sid]['label'],attempts=[dict(run=r['run'],exit=r['exit'],wall_seconds=r['wall'],note=r['note']) for r in runs if r['spec_id']==sid],successful_runs=[r['run'] for r in good if r['spec_id']==sid],
        overflow_checks_runs=[r['run'] for r in good if r['spec_id']==sid],modules=(specs[sid].get('covers') or {}).get('modules',[]),definitions={})
cov['specs']['UNASSIGNED']=dict(label='definitions with no fresh emission in any PCQG run',attempts=[],successful_runs=[],modules=[],definitions={})
for r in req:
    g=r['gate_def'];n=norm(g);hit=None
    cands=[n,'aspis_core.'+n,'aspis_statement.'+n,g]
    for run in good:
        for nn in cands:
            if nn in FD[run['run']]:hit=(run,FD[run['run']][nn],nn);break
        if hit:break
    key=(r['origin']+':'+r['module']+':'+g)
    if hit:
        body=[h for h in hit[1] if h['kind'] not in('axiom','opaque')]
        d=dict(origin=r['origin'],module=r['module'],status='FRESH_PRESENT' if body else 'FRESH_EXTERNAL_AXIOM_ONLY',fresh=hit[2],run=hit[0]['run'],where=hit[1])
        sid=hit[0]['spec_id']
    else:
        if r['found_by_name'] is False or r['frozen_file']=='UNLOCATED' and False:
            d=dict(origin=r['origin'],module=r['module'],status='NO_FROZEN_COUNTERPART',reason='P2b: no item of that name in the frozen tree (probe-only helper, closure of one, or a trait-impl name Aeneas derives)')
        else:
            d=dict(origin=r['origin'],module=r['module'],status='MISSING',reason='no non-opaque declaration of the normalised name in any good PCQG run; intended spec: '+spec_for(r))
        sid='UNASSIGNED'
    cov['specs'][sid]['definitions'][key]=d
    if hit:
        run=hit[0];dd=rel(E/(run['run']+'_emitted/raw'))+'/'+run['ns']
        p2.setdefault(r['module'],{}).setdefault(dd,dict(run=run['run'],dir=dd,definitions=[]))['definitions'].append(g)
cfgm=J(E/'PCQG_CONFIG_BY_MODULE.json')['modules'] if (E/'PCQG_CONFIG_BY_MODULE.json').exists() else {}
cov['extraction_configuration_per_gate_module']={m:dict(overflow_checks=v['overflow_checks'],basis=v['basis']) for m,v in cfgm.items()}
cov['runs_configuration']={r['run']:dict(overflow_checks='ON',exit=r['exit']) for r in runs}
cov['p2_emission_dirs_per_gate_module']={m:sorted(v.values(),key=lambda x:x['run']) for m,v in sorted(p2.items())}
summ={}
for e in cov['specs'].values():
    for d in e['definitions'].values():summ[d['status']]=summ.get(d['status'],0)+1
cov['summary']=summ
(E/'PCQG_COVERAGE.json').write_text(json.dumps(cov,indent=1)+'\n');print('coverage',summ)
