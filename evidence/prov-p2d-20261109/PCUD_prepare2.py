#!/usr/bin/env python3
"""PCUD_prepare2.py PLAN.json OUT.json [modules...]: greedy multi-pass cover of the reached definitions of each a-lane module.
Pass 1 = best (raw fresh dir, gate candidate) pair; later passes cover the reached definitions not yet text-identical to an earlier pass's fresh dir.
Identity here is the partition's own measure (PCUD_partition.segments norm_sha per Rust symbol); the Lean compile against the gate constants is the real check."""
import json,subprocess,sys,re
from pathlib import Path
sys.dont_write_bytecode=True
sys.path.insert(0,'.')
import PCUD_gen_equalities as G, PCUD_partition as PT
def show(p):
    r=subprocess.run(['git','show',f'research:{p}'],capture_output=True)
    return r.stdout.decode('utf-8','replace') if r.returncode==0 else None
S='/private/tmp/claude-501/-Users-dominic-ZK/e51a42a3-64c9-4a23-9ea1-f7bf410e2db1/scratchpad/part'
FSF=json.load(open(S+'/fresh_symbol_files.json'));IDX=json.load(open(S+'/lean_index.json'));CLS=json.load(open(S+'/classified.json'))
SHA2GP={}
for g,v in IDX.items(): SHA2GP.setdefault(v['sha256'],(g,v['paths']))
plan=json.load(open(sys.argv[1]));P=json.load(open('PCUD_PARTITION.json'))['modules'];out={};only=sys.argv[3:]
Path('inputs').mkdir(exist_ok=True)
def segs_of(t):
    d={}
    for seg in PT.segments(t): d.setdefault(seg['symn'],set()).add(seg['norm_sha'])
    return d
for m,pl in plan.items():
    if only and m not in only: continue
    mod=P[m];reached=set(mod['reached_definitions'])
    cands=[]
    for cand in mod['candidates']:
        t=show(cand['paths'][0])
        if t is None: continue
        ns=re.findall(r'(?m)^namespace\s+(\S+)',G.uncomment(t))
        if len(ns)!=1: continue
        gs={}
        for seg in PT.segments(t):
            hm=re.search(r'\b(?:def|abbrev|structure|inductive|opaque|axiom|theorem|instance)\s+(\S+)',seg['head'])
            ln=(ns[0]+'.'+hm.group(1)) if hm else None
            if ln in reached: gs[ln]=(seg['symn'],seg['norm_sha'])
        cands.append((cand,t,gs))
    fname='Types.lean' if pl['kind']=='Types' else 'Funs.lean'
    dirs=[]
    for fdir,_ in pl['rank']:
        main=show(fdir+'/'+fname)
        if main is not None: dirs.append((fdir,main,segs_of(main)))
    # non-raw single-namespace fresh files (pinned retained emissions) as pseudo directories
    seen=set(d[0] for d in dirs);shas=set()
    for n in reached:
        for sh in FSF.get(CLS[m]['defs'].get(n,{}).get('symn'),[]): shas.add(sh)
    for sh in shas:
        g,paths=SHA2GP[sh];p0=paths[0]
        if '/raw/' in p0 or p0 in seen: continue
        txt=PT.cat_oid(g)
        if len(re.findall(r'(?m)^namespace\s+(\S+)',G.uncomment(txt)))!=1: continue
        dirs.append(('FILE:'+p0,txt,segs_of(txt)))
    remaining=set(reached);passes=[]
    while remaining and len(passes)<4:
        best=None
        for i,(fdir,main,fs) in enumerate(dirs):
            for cand,t,gs in cands:
                cov={n for n in remaining if n in gs and gs[n][1] in fs.get(gs[n][0],())}
                key=(len(cov),-i)
                if cov and (best is None or key>best[0]): best=(key,fdir,main,cand,t,cov)
        if best is None: break
        _,fdir,main,cand,t,cov=best
        tag='' if not passes else f'_p{len(passes)+1}'
        safe=m.replace('.','_')+tag;d=Path('inputs')/('fresh_'+safe);d.mkdir(exist_ok=True)
        if fdir.startswith('FILE:'):
            (d/'Funs.lean').write_text(main)
            if pl['kind']!='Funs' or True: (d/'Types.lean').write_text(main)
        else:
          for n in ('Funs.lean','Types.lean','FunsExternal_Template.lean','TypesExternal_Template.lean'):
            x=show(fdir+'/'+n)
            if x is not None: (d/n).write_text(x)
        Path('inputs/gate_'+safe+'.lean').write_text(t)
        gt=None
        if pl['kind']=='Funs':
            tp=cand['paths'][0].replace('Funs.lean','Types.lean');tt=show(tp)
            if tt is not None and tp!=cand['paths'][0]: gt='inputs/gatetypes_'+safe+'.lean';Path(gt).write_text(tt)
        nss=re.findall(r'(?m)^namespace\s+(\S+)',G.uncomment(main))
        passes.append({'tag':tag,'fresh_dir':fdir,'fresh_ns':nss,'gate_candidate_sha':cand['sha256'],'gate_path':cand['paths'][0],'gate_types_path':gt,'covers':sorted(cov)})
        remaining-=cov
    out[m]={'kind':pl['kind'],'status':'PREPARED' if passes else 'NO_IDENTICAL_RAW_FRESH','passes':passes,'uncovered_after_passes':sorted(remaining),'nreached':len(reached)}
    print(m,[len(p['covers']) for p in passes],len(remaining))
Path(sys.argv[2]).write_text(json.dumps(out,indent=1))
