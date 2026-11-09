#!/usr/bin/env python3
"""PCUC_prepare.py OUT.json MODULE...: plan (fresh dir, gate candidate) passes for the P2c cluster.
Derived from PCUD_prepare.py (P2d). Changes: the fresh directories are ONLY the overflow-checks-on emission dirs listed in
PCUC_ALLOWED_DIRS (PCQC_COVERAGE map + PCQ_E037-E040 + other PCQC redo dirs); no scratchpad symbol map; coverage = presence of
a same-Rust-symbol declaration in the fresh file (ties prefer text-identical)."""
import json,subprocess,sys,re
from pathlib import Path
sys.dont_write_bytecode=True
sys.path.insert(0,'.')
import PCUC_gen_equalities as G, PCUC_partition as PT
def show(p):
    r=subprocess.run(['git','show','HEAD:'+p],capture_output=True)
    return r.stdout.decode('utf-8','replace') if r.returncode==0 else None
ALLOWED=json.load(open('PCUC_ALLOWED_DIRS.json'))
P=json.load(open('PCUC_PARTITION.json'))['modules']
GT=json.load(open('PCUC_GATE_TYPES.json'))
out={};Path('inputs').mkdir(exist_ok=True)
def segs_of(t):
    d={}
    for seg in PT.segments(t): d.setdefault(seg['symn'],set()).add(seg['norm_sha'])
    return d
def kind_of(m): return 'Types' if m.endswith('.Types') else ('Funs' if m.endswith('.Funs') else 'single')
targets=[]
for m in sys.argv[2:]:
    if kind_of(m)=='single': targets+=[(m,m,'Funs'),(m+'@T',m,'Types')]
    else: targets.append((m,m,kind_of(m)))
for tkey,m,view in targets:
    mod=P[m];reached=set(mod['reached_definitions']);kind=kind_of(m);fname=view+'.lean'
    sfx="_T" if tkey.endswith('@T') else ''
    D=[]
    for d in ALLOWED:
        txt=show('evidence/'+d+'/'+fname) if not d.startswith('evidence/') else show(d+'/'+fname)
        if txt is None: continue
        D.append((d,txt,segs_of(txt)))
    cands=[]
    for cand in mod['candidates']:
        t=show(cand['paths'][0])
        if t is None: continue
        ns=re.findall(r'(?m)^namespace\s+(\S+)',G.uncomment(t))
        cut=None
        if len(ns)>1:
            # PCUC classification C-NS: a gate file with extra hand-appended namespaces (NFY_Part042: Slice.Insts...) is cut after the end of its first
            # (Aeneas) namespace for the interface text only; equalities are stated against the compiled constants either way.
            em=re.search(r'(?m)^end '+re.escape(ns[0])+r'\s*$',t)
            if not em: continue
            cut=t[em.end():];t=t[:em.end()]+'\n';ns=ns[:1]
            if len(re.findall(r'(?m)^namespace\s+(\S+)',G.uncomment(t)))!=1: continue
        if len(ns)!=1: continue
        gs={}
        for seg in PT.segments(t):
            hm=re.search(r'\b(?:def|abbrev|structure|inductive|opaque|axiom|theorem|instance)\s+(\S+)',seg['head'])
            ln=(ns[0]+'.'+hm.group(1)) if hm else None
            if ln in reached: gs[ln]=(seg['symn'],seg['norm_sha'])
        cand=dict(cand,gate_text_cut_tail=cut);cands.append((cand,t,gs))
    remaining=set(reached);passes=[]
    while remaining and len(passes)<6:
        best=None
        for i,(fdir,main,fs) in enumerate(D):
            for cand,t,gs in cands:
                cov={n for n in remaining if n in gs and gs[n][0] in fs}
                ident={n for n in cov if gs[n][1] in fs[gs[n][0]]}
                key=(len(cov),len(ident),-i)
                if cov and (best is None or key>best[0]): best=(key,fdir,main,cand,t,cov)
        if best is None: break
        _,fdir,main,cand,t,cov=best
        tag=sfx if not passes else f'{sfx}_p{len(passes)+1}'
        safe=m.replace('.','_')+tag;d=Path('inputs')/('fresh_'+safe);d.mkdir(exist_ok=True)
        base='evidence/'+fdir if not fdir.startswith('evidence/') else fdir
        for n in ('Funs.lean','Types.lean','FunsExternal_Template.lean','TypesExternal_Template.lean'):
            x=show(base+'/'+n)
            if x is not None: (d/n).write_text(x)
        Path('inputs/gate_'+safe+'.lean').write_text(t)
        gt=None
        if kind=='Funs' or (kind=='single' and view=='Funs'):
            tp=cand['paths'][0].replace('Funs.lean','Types.lean');tt=show(tp)
            if tt is not None and tp!=cand['paths'][0]: gt='inputs/gatetypes_'+safe+'.lean';Path(gt).write_text(tt)
        # PCUC override: Types for Funs views come from the compiled Types module (or the earlier part), see PCUC_GATE_TYPES.json
        ov=GT.get(m)
        if ov and view=='Funs':
            txt=''
            for q in ov:
                x=show(q)
                if x is None: raise SystemExit('missing '+q)
                em2=re.search(r'(?m)^end AspisR20Request\s*$',x) if 'NFY_Part042' in q else None
                txt+=(x[:em2.end()]+'\n' if em2 else x)+'\n'
            gt='inputs/gatetypes_'+safe+'.lean';Path(gt).write_text(txt+(t if kind=='single' else ''))
        nss=re.findall(r'(?m)^namespace\s+(\S+)',G.uncomment(main))
        passes.append({'tag':tag,'fresh_dir':fdir,'fresh_ns':nss,'gate_candidate_sha':cand['sha256'],'gate_path':cand['paths'][0],'gate_types_path':gt,'covers':sorted(cov),'n_gate_candidates':len(cands),'gate_text_cut_tail_bytes':(len(cand['gate_text_cut_tail']) if cand.get('gate_text_cut_tail') else 0)})
        remaining-=cov
    out[tkey]={'module':m,'view':view,'kind':kind,'status':'PREPARED' if passes else 'NO_FRESH_EMISSION','passes':passes,'uncovered_after_passes':sorted(remaining),'nreached':len(reached)}
    print(tkey,kind,[len(p['covers']) for p in passes],len(remaining),flush=True)
Path(sys.argv[1]).write_text(json.dumps(out,indent=1))
