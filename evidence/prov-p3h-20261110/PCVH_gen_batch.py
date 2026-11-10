#!/usr/bin/env python3
"""PCVH_gen_batch.py: item 2 targets (ON emission pinned, never compared). Usage: PCVH_gen_batch.py [module ...]
Reads ../prov-p1i-20261110/PCQI_REMAINING.json (ON_EMISSION_EXISTS_NOT_COMPARED), generates PRVEq_<M>_n1.lean per module."""
import json,subprocess,sys,os,re,glob
sys.dont_write_bytecode=True
H=os.path.dirname(os.path.abspath(__file__));EV=os.path.dirname(H);REPO=os.path.dirname(os.path.dirname(EV))
rem=json.load(open(EV+'/prov-p1i-20261110/PCQI_REMAINING.json'))['by_module']
part=json.load(open(EV+'/prov-plan-20261108/PRV_PARTITION.json'))['modules']
want=sys.argv[1:];res={}
def gate(m):
    dest=f'{H}/inputs/gate_{m.replace(".","_")}.lean'
    if os.path.exists(dest): return dest
    for c in part.get(m,{}).get('candidates',[]):
        t=subprocess.run(['git','-C',REPO,'show','research:'+c['path']],capture_output=True,text=True)
        if t.returncode==0: open(dest,'w').write(t.stdout);return dest
for m,l in rem.items():
    if want and m not in want: continue
    ds=[x for x in l if x['class_']=='ON_EMISSION_EXISTS_NOT_COMPARED']
    if not ds: continue
    g=gate(m)
    if not g: res[m]='NOGATE';continue
    gt=open(g).read();ns=re.findall(r'(?m)^namespace\s+(\S+)',gt)
    runs=[]
    for x in ds:
        for r in re.findall(r'[A-Z]{2,4}_E\d+',x['detail']):
            if r not in runs: runs.append(r)
    only=[]
    for x in ds:
        d=x['definition']
        for n in ns:
            if d.startswith(n+'.'): d=d[len(n)+1:];break
        only.append(d)
    kind='Types.lean' if m.endswith('Types') else 'Funs.lean'
    safe=m.replace('.','_');done=False
    cands=[]
    for r in runs:
        cands+=glob.glob(f'{EV}/*/{r}_emitted/raw/*/{kind}')
    if not cands: res[m]='NO_EMISSION_DIR '+','.join(runs);continue
    tm=m[:-5]+'.Types' if m.endswith('.Funs') else None
    gts=gate(tm) if tm and tm in part else g
    gts=gts or g
    json.dump(only,open(f'{H}/gen/only_{safe}_n1.json','w'))
    for i,c in enumerate(cands):
        fd=os.path.dirname(c);fns=re.findall(r'(?m)^namespace\s+(\S+)',open(c).read())[0]
        tag=f'_n{i+1}'
        cmd=['python3','-B','PCVH_gen_equalities.py','--module',m,'--tag',tag,'--fresh-dir',fd,'--fresh-ns',fns,'--gate-source',g,'--gate-types-source',gts,'--out',f'PRVEq_{safe}{tag}.lean','--report',f'gen/{safe}{tag}.report.json','--state-out',f'gen/{safe}{tag}.state.json','--prune-fresh','--only',f'gen/only_{safe}_n1.json']
        if len(set(ns))>1:
            dn=[n for n in ns if ds[0]['definition'].startswith(n+'.')]
            cmd+=['--gate-namespace',(dn or ns)[0]]
        r=subprocess.run(cmd,cwd=H,capture_output=True,text=True)
        res[f'{m}{tag}']=dict(rc=r.returncode,fresh=os.path.relpath(fd,EV),n=len(only),err=r.stderr.strip()[-200:])
json.dump(res,open(H+'/gen/batch_summary.json','w'),indent=1)
for k,v in res.items(): print(k,str(v)[:230])
