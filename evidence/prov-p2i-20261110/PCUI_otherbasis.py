#!/usr/bin/env python3
"""PCUI_basis.py: for each deployed_splitB-cone definition that PCXB counts OPEN with reason WRONG_BASIS, find committed
emissions (any recorded configuration) whose declaration text is identical (generator norm_decl) to the gate declaration.
Output PCUI_OTHERBASIS_CANDIDATES.json. Identical text on a configuration-labelled emission is the precondition for a rfl proof."""
import json,glob,os,re,subprocess,sys,collections
sys.dont_write_bytecode=True
HERE=os.path.dirname(os.path.abspath(__file__));EV=os.path.dirname(HERE);REPO=os.path.dirname(os.path.dirname(EV))
sys.path.insert(0,EV+'/prov-p2h-20261109')
import PCUH_gen_equalities as G
RM=json.load(open(HERE+'/PCUI_REMAINING.json'));TS={x['definition']:x for x in RM['items'] if x['cls'] in('NOT_COVERED_NO_TEXT_IDENTICAL_RECEIPTED_EMISSION','FAILED_FRESH_OR_PROOF','OTHER')}
PROV=json.load(open(EV+'/prov-p6c-20261109/PCXB_PROVENANCE.json'))
PART=json.load(open(EV+'/prov-p5-20261109/PCT_PARTITION.json'))
CFG=json.load(open(HERE+'/PCUI_EMISSION_CONFIG.json'))
IDX=json.load(open(EV+'/prov-p2f-20261109/PCUF_EMISSION_INDEX.json'))
onidx={}
for k,v in IDX.items(): onidx[os.path.dirname(os.path.dirname(k))]=v
def gitshow(p):
    r=subprocess.run(['git','-C',REPO,'show','research:'+p],capture_output=True,text=True)
    return r.stdout if r.returncode==0 else None
wb=collections.defaultdict(list)
for mn,m in PROV['modules'].items():
    for dn,df in m['definitions'].items():
        if dn in TS: wb[mn].append((dn,df))
def blocks_of(text):
    return {b['name']:G.norm_decl(b) for b in G.parse_blocks(text) if b['kind']=='decl'}
cache={}
def emission_blocks(path):
    if path not in cache: cache[path]=blocks_of(open(path).read())
    return cache[path]
emis=[]
for d in sorted(glob.glob(EV+'/*/*_emitted/raw/*')):
    if not os.path.isdir(d): continue
    rel=os.path.relpath(d,EV);top=rel.split('/raw/')[0]
    cfg=CFG.get(top,{}).get('config','UNRECORDED')
    e=IDX.get(rel)
    if e and not e.get('eligible',True): continue
    if e: cfg=e['overflow_checks'] if e['overflow_checks'] in('ON','OFF') else cfg
    for f in ('Funs.lean','Types.lean'):
        if os.path.exists(d+'/'+f): emis.append((rel,cfg,f,d+'/'+f))
res={}
for mn,lst in wb.items():
    srcs=None
    cands=PART['modules'].get(mn,{}).get('candidates',[])
    txt=None;used=None
    for c in cands:
        for p in c['paths']:
            t=gitshow(p)
            if t: txt=t;used=p;break
        if txt:break
    if not txt:
        res[mn]=dict(error='no gate source',defs=[d for d,_ in lst]);continue
    nsm=re.findall(r'(?m)^namespace\s+(\S+)',txt);ns=nsm[0] if nsm else ''
    gb=blocks_of(txt)
    out=[]
    for dn,df in lst:
        rel=dn[len(ns)+1:] if dn.startswith(ns+'.') else dn
        gtxt=gb.get(rel)
        hits=[]
        if gtxt:
            for (er,cfg,f,path) in emis:
                eb=emission_blocks(path)
                if eb.get(rel)==gtxt: hits.append((er,cfg,f))
        out.append(dict(definition=dn,rel=rel,gate_found=gtxt is not None,arith=df['arithmetic_class'],hits=hits))
    res[mn]=dict(gate_source=used,namespace=ns,defs=out)
json.dump(res,open(HERE+'/PCUI_OTHERBASIS_CANDIDATES.json','w'),indent=1)
tot=collections.Counter()
for mn,r in res.items():
    if 'defs' in r and r.get('error') is None and isinstance(r['defs'],list) and r['defs'] and isinstance(r['defs'][0],dict):
        c=collections.Counter()
        for x in r['defs']:
            cf=sorted({h[1] for h in x['hits']})
            c['gate_missing' if not x['gate_found'] else ('+'.join(cf) if cf else 'NO_IDENTICAL_EMISSION')]+=1
        print(mn,dict(c));tot.update(c)
    else: print(mn,r.get('error'))
print(dict(tot))
