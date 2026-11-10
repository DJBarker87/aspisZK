#!/usr/bin/env python3
import json,re,glob,collections
S='/private/tmp/claude-501/-Users-dominic-ZK/e51a42a3-64c9-4a23-9ea1-f7bf410e2db1/scratchpad/'
fh=json.load(open(S+'ref/evidence/prov-p1m-20261110/PCQJ_FIRST_HALF.json'));sh=json.load(open('PCQL_SECOND_HALF.json'))
cred=json.load(open('PCQL_credit_out.json'))
proved={};oblig={}
for a,v in cred.items():
    m=v['module'][len('PRVEq_'):];safe=m.rsplit('_n3b',1)[0]
    nm=json.load(open(f'gen/nm_{safe}_n3.json'))
    for t in v['theorems']:
        f=t['theorem'].split('_n3.',1)[1];proved[(safe,nm.get(f,f))]=a
    for o in v['obligations']:
        mm=re.search(r'PRV-OBLIGATION \(([^)]*)\)[^:]*: PRVEq\.\S+?_n3\.(\S+) :',o)
        if mm:oblig[(safe,nm.get(mm.group(2),mm.group(2)))]=mm.group(1)
batch={}
for f in glob.glob('gen/PCQL_BATCH_*.jsonl'):
    for l in open(f):
        d=json.loads(l);batch[d['module']]=d
m1={'AspisR1DotPushLocal.Funs','RPz7_AspisR1CircleSampleWrapper_Funs','AspisR1Post25Sampler.Funs','AspisR1CanonicalDotFinish.Funs','CurrentClaimSumModel','NFS_AccumPart00','FinishCandidateExplicitOps'}
out=[]
for half,L in (('first',fh),('second',sh)):
    for x in L:
        m=x['module'];safe=m.replace('.','_');d=x['definition']
        ns=re.findall(r'(?m)^namespace\s+(\S+)',open(f'inputs/gate_{safe}.lean').read())[0] if glob.glob(f'inputs/gate_{safe}.lean') else None
        rel=d[len(ns)+1:] if ns and d.startswith(ns+'.') else d
        if (safe,rel) in proved: st='EMITTED+PROVED';det=f'scope {proved[(safe,rel)]} exit 0, standard axioms'
        elif (safe,rel) in oblig: st='EMITTED+FAILED';det='generator obligation: '+oblig[(safe,rel)]+' (stage-1 rfl and stage-2 delta+rfl did not close it; not a counterexample)'
        elif m in m1 and m in batch and rel in set(json.load(open(f'gen/nm_{safe}_m1.json')).values()) | {rel for rel in [rel] if False}: st='EMITTED_NOT_COMPILED';det='generated against E006 emission; Lean budget (20) exhausted after the exit-1 probe; not credited'
        elif m in batch and batch[m].get('status')=='NO_GATE_SOURCE': st='NOT_PROCESSED';det='no unique gate source by import match'
        elif m in batch and batch[m].get('report',{}).get('common_declarations')==0: st='NO_COMMON_NAME';det='module processed against E006; no gate declaration name has a unique fresh counterpart by the recorded name map (gate differs from frozen in naming or source shape; not forced)'
        elif m in batch: st='NO_COMMON_NAME_OR_NOT_COMPARED';det='processed; this definition has no recorded fresh counterpart'
        else: st='NOT_PROCESSED';det='module not attempted (extraction roots for its frozen counterpart not reached, or not scheduled)'
        out.append(dict(half=half,module=m,definition=d,rows=x['rows'],status=st,detail=det))
c=collections.Counter((o['half'],o['status']) for o in out);print(c)
json.dump(dict(schema='PCQL_STATUS/1',target_established=False,counts={f'{a}:{b}':n for (a,b),n in c.items()},definitions=out),open('PCQL_STATUS.json','w'),indent=1)
