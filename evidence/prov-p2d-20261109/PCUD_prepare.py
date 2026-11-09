#!/usr/bin/env python3
"""PCUD_prepare.py OUT.json MODULES_JSON : plan (fresh dir, gate candidate) passes for the c1/c2 cluster of P2d.
Derived from PCT_prepare2.py (P5). Change: the coverage measure is PRESENCE of a same-Rust-symbol declaration in the fresh frozen file
(not text identity), because the modules of this cluster are COVERED_DIFFERS/partly IDENTICAL by construction; ties prefer text-identical
(partition norm_sha). The Lean compile against the gate constants is the actual check; a wrong gate candidate gives a Lean error, never a false equality."""
import json,subprocess,sys,re,collections
from pathlib import Path
sys.dont_write_bytecode=True
sys.path.insert(0,'.')
import PCUD_gen_equalities as G, PCUD_partition as PT
def show(p):
    r=subprocess.run(['git','show','HEAD:'+p],capture_output=True)
    return r.stdout.decode('utf-8','replace') if r.returncode==0 else None
S='/private/tmp/claude-501/-Users-dominic-ZK/e51a42a3-64c9-4a23-9ea1-f7bf410e2db1/scratchpad/part'
FSF=json.load(open(S+'/fresh_symbol_files.json'));IDX=json.load(open(S+'/lean_index.json'));CLS=json.load(open(S+'/classified.json'))
SHA2GP={}
for g,v in IDX.items(): SHA2GP.setdefault(v['sha256'],(g,v['paths']))
P=json.load(open('PCUD_PARTITION.json'))['modules']
mods=json.load(open(sys.argv[2])); out={}
Path('inputs').mkdir(exist_ok=True)
def segs_of(t):
    d={}
    for seg in PT.segments(t): d.setdefault(seg['symn'],set()).add(seg['norm_sha'])
    return d
def kind_of(m):
    return 'Types' if m.endswith('.Types') else ('Funs' if m.endswith('.Funs') else 'single')
for m in mods:
    mod=P[m];reached=set(mod['reached_definitions']);kind=kind_of(m)
    cl=CLS.get(m,{}).get('defs',{})
    symn={n:(cl.get(n) or {}).get('symn') or mod['reached_definitions'][n]['rust'] for n in reached}
    # candidate fresh dirs from the frozen symbol->file map
    dirs={}
    for n in reached:
        for sh in FSF.get(symn[n],[]):
            g,paths=SHA2GP[sh]
            for p0 in paths:
                if '/raw/' in p0 and p0.rsplit('/',1)[1] in('Funs.lean','Types.lean'): dirs.setdefault(p0.rsplit('/',1)[0],None)
            if not any('/raw/' in p0 for p0 in paths):
                p0=paths[0]
                if p0.rsplit('/',1)[1] in('Funs.lean','Types.lean') or True: dirs.setdefault('FILE:'+p0,sh)
    fname='Types.lean' if kind=='Types' else 'Funs.lean'
    D=[]
    for d,sh in dirs.items():
        if d.startswith('FILE:'):
            txt=PT.cat_oid(SHA2GP[sh][0])
            if len(re.findall(r'(?m)^namespace\s+(\S+)',G.uncomment(txt)))!=1: continue
            D.append((d,txt,segs_of(txt)))
        else:
            txt=show(d+'/'+fname)
            if txt is None: continue
            D.append((d,txt,segs_of(txt)))
    HAS={d:int(d.startswith('FILE:') or (show(d+'/Types.lean') is not None and show(d+'/Funs.lean') is not None)) for d,_,_ in D}
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
    remaining=set(reached);passes=[]
    while remaining and len(passes)<4:
        best=None
        for i,(fdir,main,fs) in enumerate(D):
            for cand,t,gs in cands:
                cov={n for n in remaining if n in gs and gs[n][0] in fs}
                ident={n for n in cov if gs[n][1] in fs[gs[n][0]]}
                key=(len(cov),len(ident),HAS.get(fdir,0),-i)
                if cov and (best is None or key>best[0]): best=(key,fdir,main,cand,t,cov)
        if best is None: break
        _,fdir,main,cand,t,cov=best
        tag='' if not passes else f'_p{len(passes)+1}'
        safe=m.replace('.','_')+tag;d=Path('inputs')/('fresh_'+safe);d.mkdir(exist_ok=True)
        if fdir.startswith('FILE:'):
            (d/'Funs.lean').write_text(main);(d/'Types.lean').write_text(main)
        else:
          for n in ('Funs.lean','Types.lean','FunsExternal_Template.lean','TypesExternal_Template.lean'):
            x=show(fdir+'/'+n)
            if x is not None: (d/n).write_text(x)
        Path('inputs/gate_'+safe+'.lean').write_text(t)
        gt=None
        if kind=='Funs':
            tp=cand['paths'][0].replace('Funs.lean','Types.lean');tt=show(tp)
            if tt is not None and tp!=cand['paths'][0]: gt='inputs/gatetypes_'+safe+'.lean';Path(gt).write_text(tt)
        nss=re.findall(r'(?m)^namespace\s+(\S+)',G.uncomment(main))
        passes.append({'tag':tag,'fresh_dir':fdir,'fresh_ns':nss,'gate_candidate_sha':cand['sha256'],'gate_path':cand['paths'][0],'gate_types_path':gt,'covers':sorted(cov),
                       'n_gate_candidates':len(cands)})
        remaining-=cov
    out[m]={'kind':kind,'status':'PREPARED' if passes else 'NO_FRESH_EMISSION','passes':passes,'uncovered_after_passes':sorted(remaining),'nreached':len(reached)}
    print(m,kind,[len(p['covers']) for p in passes],len(remaining),flush=True)
Path(sys.argv[1]).write_text(json.dumps(out,indent=1))
