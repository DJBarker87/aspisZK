#!/usr/bin/env python3
"""PCXK_plan.py: group the 78 corrected copies into scopes of <= 4 files (sequential in one capped scope). Wall estimate = max wall of the original exit-0 receipts
(evidence/<job>/*_ATTEMPTS.jsonl), else 0.12 s per line. Heavy files (est >= 100 s) run alone; packing is first-fit decreasing to est sum <= 240 s. Writes PCXK_PLAN.json."""
import json,glob,os
here=os.path.dirname(os.path.abspath(__file__)); os.chdir(os.path.join(here,'..','..'))
files=json.load(open(here+'/PCXK_FILES.json'))['files']; est={}
for r in files:
    d=r['original'].split('/')[1]; b=os.path.basename(r['original'])[:-5]; w=[]
    for a in glob.glob(f'evidence/{d}/*_ATTEMPTS.jsonl'):
        for l in open(a):
            try:e=json.loads(l)
            except Exception: continue
            if e.get('event')!='result': continue
            for s in (e.get('steps') or [e]):
                if s.get('module')==b and s.get('wall_seconds'): w.append(float(s['wall_seconds']))
    n=sum(1 for _ in open(here+'/'+r['copy']))
    est[r['copy']]=(max(w),'receipt') if w else (0.12*n,'lines')
order=sorted(est,key=lambda k:-est[k][0]); scopes=[]
for k in order:
    for s in scopes:
        if len(s['files'])<4 and s['est']+est[k][0]<=240 and s['est']<100 and est[k][0]<100: s['files'].append(k); s['est']+=est[k][0]; break
    else: scopes.append(dict(files=[k],est=est[k][0]))
for i,s in enumerate(scopes,1): s['attempt']='PCXK_L%03d'%i; s['modules']=[os.path.basename(f)[:-5] for f in s['files']]
json.dump(dict(schema='PCXK_PLAN/1',estimates={k:dict(seconds=round(v[0],1),basis=v[1]) for k,v in est.items()},scopes=scopes),open(here+'/PCXK_PLAN.json','w'),indent=1)
print(len(scopes),[round(s['est']) for s in scopes])
