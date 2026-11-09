#!/usr/bin/env python3
"""PCT_prepare.py: choose gate-source candidate and fresh dir per a-lane module, fetch inputs with git show, run PCT_gen_equalities (probe round).
Selection rule (recorded in PCT_CLASSIFICATIONS.json, PCT-C1): the fresh dir is the raw Aeneas output directory covering most reached definitions
(plan from fresh_symbol_files of PCT_partition.py); the gate-source candidate is the partition candidate whose declarations match the fresh
declarations (norm_decl equal) for the most reached definitions. The Lean compile against the gate constants is the actual check."""
import json,subprocess,sys,re,os
from pathlib import Path
sys.dont_write_bytecode=True
sys.path.insert(0,'.')
import PCT_gen_equalities as G
import PCT_partition as PT
REV='research'
def show(p):
    r=subprocess.run(['git','show',f'{REV}:{p}'],capture_output=True)
    return r.stdout.decode('utf-8','replace') if r.returncode==0 else None
plan=json.load(open(sys.argv[1]));P=json.load(open('PCT_PARTITION.json'))['modules']
only=sys.argv[2:]
Path('inputs').mkdir(exist_ok=True)
res={}
for m,pl in plan.items():
    if only and m not in only: continue
    mod=P[m];reached=set(mod['reached_definitions'])
    if not pl['rank']: res[m]={'status':'NO_RAW_FRESH_DIR'};continue
    def segs_of(t):
        d={}
        for seg in PT.segments(t): d.setdefault(seg['symn'],set()).add(seg['norm_sha'])
        return d
    cands=[]
    for cand in mod['candidates']:
        t=show(cand['paths'][0])
        if t is None: continue
        ns=re.findall(r'(?m)^namespace\s+(\S+)',G.uncomment(t))
        if len(ns)!=1: continue
        gs=[]
        for seg in PT.segments(t):
            hm=re.search(r'\b(?:def|abbrev|structure|inductive|opaque|axiom|theorem|instance)\s+(\S+)',seg['head'])
            ln=(ns[0]+'.'+hm.group(1)) if hm else None
            if ln in reached: gs.append((seg['symn'],seg['norm_sha']))
        cands.append((cand,t,gs))
    best=None
    for i,(fdir,_n) in enumerate(pl['rank']):
        fname='Types.lean' if pl['kind']=='Types' else 'Funs.lean'
        main=show(fdir+'/'+fname)
        if main is None: continue
        fs=segs_of(main)
        for cand,t,gs in cands:
            score=sum(1 for sy,sh in gs if sh in fs.get(sy,()))
            key=(score,-i)
            if best is None or key>best[0]: best=(key,fdir,cand,t,main,score)
    if best is None: res[m]={'status':'NO_PAIR'};continue
    _,fdir,cand,gtext,main,score=best
    ft=show(fdir+'/Funs.lean');ty=show(fdir+'/Types.lean')
    if pl['kind']=='Funs' and ft is None: res[m]={'status':'FRESH_FILE_MISSING','dir':fdir};continue
    safe=m.replace('.','_');d=Path('inputs')/('fresh_'+safe);d.mkdir(exist_ok=True)
    for n,t in (('Funs.lean',ft),('Types.lean',ty)):
        if t is not None: (d/n).write_text(t)
    for n in ('FunsExternal_Template.lean','TypesExternal_Template.lean'):
        t=show(fdir+'/'+n)
        if t is not None: (d/n).write_text(t)
    nss=re.findall(r'(?m)^namespace\s+(\S+)',G.uncomment(main))
    best=(score,cand['sha256'],cand['paths'][0],gtext)
    g=Path('inputs')/('gate_'+safe+'.lean');g.write_text(best[3])
    gt=None
    if pl['kind']=='Funs':
        tp=best[2].replace('Funs.lean','Types.lean');tt=show(tp)
        if tt is not None and tp!=best[2]: gt=Path('inputs')/('gatetypes_'+safe+'.lean');gt.write_text(tt)
    res[m]={'status':'PREPARED','fresh_dir':fdir,'fresh_ns':nss,'gate_candidate_sha':best[1],'gate_path':best[2],'gate_types_path':str(gt) if gt else None,'identical_reached_defs':best[0],'ndefs':pl['ndefs'],'kind':pl['kind']}
    print(m,res[m]['status'],best[0],'/',pl['ndefs'],best[2][-60:],nss)
Path(sys.argv[1]+'.prepared.json').write_text(json.dumps(res,indent=1))
