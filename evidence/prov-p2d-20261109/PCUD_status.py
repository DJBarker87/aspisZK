#!/usr/bin/env python3
"""PCUD_status.py: per-module per-reached-definition status from the state2 files (verified by the round-2 bundle compiles)."""
import json,sys
from pathlib import Path
prep=json.load(open('gen_prepared.json'));P=json.load(open('PCUD_PARTITION.json'))['modules']
VER=json.load(open('gen/verify_attempts.json'))  # bundle -> attempt
bund=json.load(open('gen/bundles.json'));label2b={l:k for k,v in bund.items() for l in v}
out={};summary={}
for m,r in prep.items():
    mod=P[m];reached=list(mod['reached_definitions']);rs={}
    for ps in r['passes']:
        label=m.replace('.','_')+ps['tag']
        st=json.load(open(f'gen/PRVEq_{label}.state2.json'))
        rep=json.load(open(f'gen/PRVEq_{label}.report1.json')) if False else None
        gns=json.load(open(f'gen/PRVEq_{label}.report2.json'))['gate_namespace']
        for n,x in st['defs'].items():
            full=gns+'.'+n
            if full not in mod['reached_definitions']: continue
            cur=rs.get(full)
            if x['status']=='proved':
                s='PROVED_RFL' if x['stage']==1 else 'PROVED_UNFOLD'
                if cur is None or cur['status'].startswith('FAILED') or cur['status']=='NOT_COVERED': rs[full]=dict(status=s,pass_tag=ps['tag'],attempt=VER[label2b[label]],theorem=f"PRVEq.{m}{ps['tag']}.{n}")
            else:
                if cur is None or cur['status']=='NOT_COVERED': rs[full]=dict(status='FAILED',pass_tag=ps['tag'],class_=x.get('class'),error=x.get('error'),statement=f"@PRVFresh_{label}.{n} = @{gns}.{n}")
    cov={c for ps in r['passes'] for c in ps['covers']}
    for n in reached:
        if n not in rs and n in cov: rs[n]=dict(status='TEXT_IDENTICAL_ONLY',reason='text-identical to the receipted fresh emission (partition measure) but the generator emits no Lean statement for this declaration shape (inductive or non-simple structure, or fresh text dropped): not a Lean-proved equality')
        if n not in rs: rs[n]=dict(status='NOT_COVERED',reason='no verified common declaration with a text-identical receipted frozen emission found (see uncovered_after_passes)')
    cnt={}
    for v in rs.values(): cnt[v['status']]=cnt.get(v['status'],0)+1
    out[m]=dict(group='a',subgroup=mod['subgroup'],kind=r['kind'],passes=r['passes'],reached=rs,counts=cnt,rows=mod.get('n_rows'))
    summary[m]=cnt
Path('PCUD_STATUS.json').write_text(json.dumps(dict(target_established=False,note='Statements are against gate constants; the status of a Types structure is its generated Equiv or rfl; PROVED_UNFOLD = delta + rewrite with callee equalities + rfl.',modules=out),indent=1))
tot={}
for c in summary.values():
    for k,v in c.items(): tot[k]=tot.get(k,0)+v
print(tot)
for m,c in summary.items(): print(m,c)
