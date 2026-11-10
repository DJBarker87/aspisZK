#!/bin/bash
# PCXB_resolve.sh: resolve credited proving files of PCQH_ALL_STATUS.json to git paths at HEAD (read via git show; sparse list unchanged); scratch table.
cd /Users/dominic/ZK/.worktrees/pc-prov-p6c
SCR=/private/tmp/claude-501/-Users-dominic-ZK/e51a42a3-64c9-4a23-9ea1-f7bf410e2db1/scratchpad/partc
git ls-files | grep -E '\.lean$' > $SCR/all_lean_paths.txt
python3 -I -B - <<'PY'
import json, collections, subprocess, re
SCR='/private/tmp/claude-501/-Users-dominic-ZK/e51a42a3-64c9-4a23-9ea1-f7bf410e2db1/scratchpad/partc'
paths=[l.strip() for l in open(SCR+'/all_lean_paths.txt')]
by=collections.defaultdict(list)
for p in paths: by[p.split('/')[-1]].append(p)
d=json.load(open('evidence/prov-p1h-20261109/PCQH_ALL_STATUS.json'))
PHASE={'P2h':'prov-p2h','P1h':'prov-p1h','P3b':'prov-p3b','P3c':'prov-p3c','P3d':'prov-p3d','P3a':'prov-p3a','P4e':'prov-p4e','P2f':'prov-p2f','P2r':'prov-p2r','P5':'prov-p5','P2a':'prov-p2a','P2b':'prov-p2b','P2c':'prov-p2c','P2d':'prov-p2d','P2g':'prov-p2g','P4a':'prov-p4a','P4c':'prov-p4c','P4b':'prov-p4b'}
CRED={'EQUALITY_PROVED','EQUALITY_DOMAIN','CONDITIONAL_ON_BINDING'}
files=collections.defaultdict(lambda: dict(records=0,phases=set(),statuses=collections.Counter()))
unres=[]
for m,dd in d['modules'].items():
    for n,r in dd.items():
        if r['status'] not in CRED: continue
        pf=r.get('proving_file')
        if not pf: unres.append((m,n,r['status'],r['decided_by'],r.get('theorem'))); continue
        k=pf; files[k]['records']+=1; files[k]['phases'].add(r['decided_by']); files[k]['statuses'][r['status']]+=1
res={}; amb=[]; miss=[]
for pf,v in files.items():
    if '/' in pf and pf in paths: res[pf]=pf; continue
    cand=by.get(pf.split('/')[-1],[])
    if '/' in pf:
        c2=[c for c in cand if c.endswith(pf)]
        cand=c2 or cand
    if len(cand)==1: res[pf]=cand[0]
    elif not cand: miss.append(pf)
    else:
        ph=[PHASE[x] for x in v['phases'] if x in PHASE]
        c2=[c for c in cand if any(p in c for p in ph) and 'gen/' not in c and 'probe' not in c and 'failed' not in c and 'PCXA_L' not in c and 'sources/' not in c]
        if len(c2)==1: res[pf]=c2[0]
        else: amb.append((pf,cand,sorted(v['phases'])))
print(len(files),'files;',len(res),'resolved;',len(miss),'missing;',len(amb),'ambiguous;',len(unres),'records without proving_file')
for a in amb: print('AMB',a)
for a in miss: print('MISS',a)
print(collections.Counter((u[2],u[3]) for u in unres))
for u in unres[:40]: print(u)
json.dump(dict(resolved=res,missing=miss,ambiguous=amb,nofile=unres,info={k:dict(records=v['records'],phases=sorted(v['phases']),statuses=dict(v['statuses'])) for k,v in files.items()}),open(SCR+'/credited_files.json','w'))
PY
