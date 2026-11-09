#!/usr/bin/env python3
import json,re
from pathlib import Path
st=json.load(open('PCT_STATUS.json'));ctl=json.load(open('gen/ctl_results.json'));P=json.load(open('PCT_PARTITION.json'))['modules'];prep=json.load(open('gen/prepared2.json'))
# compiled-source determination from self-copy controls
for m,v in st['modules'].items():
    cands={c['sha256']:c for c in P[m]['candidates']};rows=[]
    for l,x in ctl.items():
        if x['module']!=m: continue
        rows.append(dict(control=l,attempt=x['attempt'],candidate_sha256=x['candidate_sha'],candidate_status=cands[x['candidate_sha']]['status'],common=x['common'],rfl=x['rfl'],unfold=x['unfold'],failed=x['failed'],all_common_equal=x['failed']==0 and x['common']>0))
    ok=[r for r in rows if r['all_common_equal']]
    v['compiled_source']=dict(controls=rows,consistent_candidates=[r['candidate_sha256'] for r in ok],consistent_receipted=[r['candidate_sha256'] for r in ok if r['candidate_status'] in('RECEIPTED','REPRODUCED')],
        note='not run for modules whose reached definitions were all proved against a receipted fresh emission (the equalities are against gate constants and do not depend on knowing the source text)' if not rows else 'probe-stage controls (no separate verify compile); FIn_WeightsFuns controls not run: pathological whnf on loop bodies in L019, shape retired')
Path('PCT_STATUS.json').write_text(json.dumps(st,indent=1))
q=[];rec={}
for m,v in st['modules'].items():
    for n,x in v['reached'].items():
        if x['status'] in('PROVED_RFL','PROVED_UNFOLD'): continue
        q.append(dict(module=m,definition=n,status=x['status'],queue='P3' if x['status']=='FAILED' else 'P2',goal=x.get('statement'),failure_class=x.get('class_'),last_error=x.get('error'),reason=x.get('reason'),
            compiled_source_candidates_consistent=v['compiled_source']['consistent_candidates']))
    c=v['counts']
    if c.get('NOT_COVERED') and not (c.get('PROVED_RFL') or c.get('PROVED_UNFOLD')): rec[m]=dict(to='c1',reason='no receipted frozen emission text-identical to a gate-compiled candidate was found by the Lean comparison; the partition identity was measured against a different candidate or version')
json.dump(dict(target_established=False,reclassified_modules=rec,items=q),open('PCT_FOR_P2P3.json','w'),indent=1)
for m,r in rec.items(): st['modules'][m]['reclassified']=r
Path('PCT_STATUS.json').write_text(json.dumps(st,indent=1))
tot={}
for v in st['modules'].values():
    for k,n in v['counts'].items(): tot[k]=tot.get(k,0)+n
print(tot,len(q),len(rec),list(rec))
