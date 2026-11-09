#!/usr/bin/env python3
"""Builds PCQC_COVERAGE.json, PCQC_SUPERSEDES.json, PCQC_FAILURES.json, PCQC_ON_OFF_DIFF.json, PCQC_HAND_MODELS.json
from committed receipts/emissions. Name-level presence only (equality is P2). Reads git objects via `git show research:`."""
import json,re,subprocess,sys,hashlib,lzma
from pathlib import Path
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;EV=E.parent
RP=EV/'prov-p1a-20261109';BP=EV/'prov-p1b-20261109';OP=EV/'prov-p0-20261109'
def J(p):return json.loads(Path(p).read_text())
def rel(p):return str(Path(p).resolve().relative_to(EV))
# ---------------- runs: PCQC (all on) + carried P1a overflow-on runs
runs=[]
def add(dirp,spec_file,carried):
    s=J(spec_file);run=s['run'];rc=dirp/run/'receipt.json'
    ex=J(rc)['exit_status'] if rc.exists() else None
    emit=dirp/(run+'_emitted/raw')
    runs.append(dict(run=run,spec_id=s['spec_id'],crate=s['configuration']['crate'],ns=s['configuration']['namespace'],exit=ex,
        on=bool(s.get('extra_env')),dir=dirp,carried=carried,kind=(s.get('p1c') or {}).get('kind'),earlier=(s.get('p1c') or {}).get('earlier_run'),has_emit=emit.exists(),spec=s))
for f in sorted(E.glob('PCQC_E[0-9][0-9][0-9]_spec.json')):add(E,f,False)
for n in (37,38,39,40):add(RP,RP/f'PCQ_E0{n}_spec.json',True)
good=[r for r in runs if r['exit']==0 and r['has_emit'] and r['on']]
# ---------------- spec catalog
cat={}
for f in (OP/'PCO_extract_specs.json',RP/'PCQ_extract_specs.json',BP/'PCQ_extract_specs.json'):
    for s in J(f)['specs']:
        if (s.get('covers') or {}).get('definitions') is not None:cat[s['spec_id']]=s   # later file wins (P1b catalog for S015-S022)
for f in (RP/'PCQ_extract_specs.json',):
    for s in J(f)['specs']:
        if s['spec_id'] in('S001','S002','S003','S004','S005','S006','S007','S008','S009','S010','S011','S012','S013','S014','S901') and s.get('covers'):cat[s['spec_id']]=s
for s in J(BP/'PCQ_extract_specs.json')['specs']:
    if s['spec_id'] in [f'S0{n}' for n in range(15,23)] and s.get('covers'):cat[s['spec_id']]=s
for r in runs:
    cat.setdefault(re.sub(r'[a-z]$','',r['spec_id']),r['spec'])
def fresh_defs(r):
    DEF=re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(def|structure|inductive|axiom|opaque|abbrev|theorem)\s+([^\s:(\[{]+)",re.M)
    out={}
    for f in sorted((r['dir']/(r['run']+'_emitted/raw')).glob('*/*.lean')):
        for kind,name in DEF.findall(f.read_text()):
            out.setdefault(name,[]).append(dict(file=rel(f),kind=kind,external='External' in f.name))
    return out
FD={r['run']:fresh_defs(r) for r in good}
def norm(g):
    parts=g.split('.')[1:]
    if parts and parts[0] in('aspis_core','aspis_statement'):parts=parts[1:]
    return '.'.join(parts)
base=lambda sid:re.sub(r'[a-z]$','',sid)
TYPES_ONLY={'S003','S007','S008'}
cov=dict(schema=1,target_established=False,note='name-level presence only; equality is P2. All runs listed as usable are overflow-checks-on (CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=true, RUSTFLAGS ... -C overflow-checks=yes); runs without it are never listed as usable here.',specs={})
p2={}
for sid in sorted(cat):
    sp=cat[sid]
    if re.search(r'[a-z]$',sid):continue
    if sid in('S902','S018','S006') and False:continue
    own=[r for r in runs if base(r['spec_id'])==sid]
    cand=[r for r in good if r in own]
    sib=[r for r in good if r['crate']==(sp.get('crate') or sp['configuration']['crate']) and r not in cand] if sp.get('covers') else []
    if sid not in TYPES_ONLY and not cand and not [r for r in own]:
        # spec never run in P1c and not carried: listed only if a sibling run might cover its names
        pass
    e=dict(attempts=[dict(run=r['run'],spec=r['spec_id'],exit=r['exit'],kind=r['kind'],earlier_run=r['earlier']) for r in own],
        successful_runs=[r['run'] for r in cand],definitions={},modules=sp['covers']['modules'],overflow_checks_runs=[r['run'] for r in cand],runs_without_overflow_checks=[])
    for g in [x for x in sp['covers']['definitions'] if ' ' not in x]:
        n=norm(g);hit=None;via='own'
        for r in cand+sib:
            for nn in (n,g):
                if nn in FD[r['run']]:hit=(r,FD[r['run']][nn]);n=nn;via='own' if r in cand else 'sibling_run';break
            if hit:break
        if hit:
            body=[h for h in hit[1] if h['kind'] not in('axiom','opaque')]
            e['definitions'][g]=dict(status='FRESH_PRESENT' if body else 'FRESH_EXTERNAL_AXIOM_ONLY',fresh=n,run=hit[0]['run'],via=via,where=hit[1])
        else:
            why=('no fresh definition named %s in %s'%(n,[r['run'] for r in cand+sib])) if (cand or sib) else 'no successful overflow-checks-on extraction (see PCQC_FAILURES.json)'
            e['definitions'][g]=dict(status='MISSING',reason=why)
    if not (e['attempts'] or e['successful_runs'] or any(d['status']!='MISSING' for d in e['definitions'].values())):continue
    cov['specs'][sid]=e
    for g,d in e['definitions'].items():
        if d['status']=='MISSING':continue
        r=next(x for x in good if x['run']==d['run']);dd=rel(r['dir']/(r['run']+'_emitted/raw'))+'/'+r['ns']
        for m in sp['covers']['modules']:
            p2.setdefault(m,{}).setdefault(dd,dict(run=r['run'],dir=dd,definitions=[]))['definitions'].append(g)
cov['pilot_emissions']={r['run']:dict(spec=r['spec_id'],dir=rel(r['dir']/(r['run']+'_emitted/raw'))+'/'+r['ns'],note='S903 types-only pilot (AdapterRwTypes); covers is free text in the spec, so no per-name table') for r in good if base(r['spec_id'])=='S903'}
cov['p2_emission_dirs_per_gate_module']={m:sorted(v.values(),key=lambda x:x['run']) for m,v in sorted(p2.items())}
c={}
for e in cov['specs'].values():
    for d in e['definitions'].values():c[d['status']]=c.get(d['status'],0)+1
cov['summary']=c
(E/'PCQC_COVERAGE.json').write_text(json.dumps(cov,indent=1)+'\n');print('coverage',c)
# ---------------- ON/OFF diff: same text modulo namespace and run id?
def normtext(t,ns):return re.sub(r'PC(QC|Q|O)_\w*?'+re.escape(ns.split('_',1)[1]) ,'NS',t)
diff={}
for r in runs:
    if r['kind']!='redo' or r['exit']!=0 or not r['has_emit']:continue
    old=r['earlier'];od={'PCQ_E002':RP,'PCQ_E014':RP,'PCQ_E026':RP,'PCQ_E036':RP,'PCQ_E018':RP,'PCO_E001':OP,'PCO_E004':OP}.get(old,BP)
    odir=od/(old+'_emitted/raw');ndir=r['dir']/(r['run']+'_emitted/raw')
    res={}
    for nf in sorted(ndir.glob('*/*.lean')):
        cand=list(odir.glob('*/'+nf.name))
        if not cand:res[nf.name]='no old file';continue
        a=cand[0].read_text();b=nf.read_text()
        a2=re.sub(r'P(?:CQC|CQ|CO)_','NS_',a);b2=re.sub(r'P(?:CQC|CQ|CO)_','NS_',b)
        res[nf.name]='identical_modulo_prefix' if a2==b2 else 'DIFFERS (%d vs %d bytes)'%(len(a2),len(b2))
    diff[r['run']]=dict(earlier=old,files=res,llbc_sha256_new=J(r['dir']/(r['run']+'_emitted/'+r['run']+'_PINS.json')).get('llbc_sha256'),llbc_sha256_old=J(od/(old+'_emitted/'+old+'_PINS.json')).get('llbc_sha256'))
(E/'PCQC_ON_OFF_DIFF.json').write_text(json.dumps(dict(note='Earlier (overflow-checks off) vs P1c (on) emission, after replacing the PCQ_/PCQC_/PCO_ prefix. DIFFERS means the overflow-checks flag (or tool state) changed the generated text.',runs=diff),indent=1)+'\n')
print({k:[v for v in d['files'].values()] for k,d in diff.items()})
