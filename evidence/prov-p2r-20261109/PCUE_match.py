#!/usr/bin/env python3
"""PCUE_match.py: for every P2a/P2d gate module, which reached definitions have a same-named (or prefix-mapped) declaration in an overflow-on emission."""
import json,sys,re,collections
from pathlib import Path
sys.dont_write_bytecode=True
EV=Path(__file__).resolve().parent.parent
idx=json.load(open('PCUE_EMISSION_INDEX.json'))
def status_defs():
    out={}  # module -> {full gate def: (old status, source tool)}
    a=json.load(open(EV/'prov-p2a-20261109/PCUA_EQ_STATUS.json'))['modules']
    for m,l in a.items():
        out.setdefault(m,{})
        for r in l: out[m][r['gate_definition']]=(r['status'],'P2a',r.get('fresh_emission'))
    d=json.load(open(EV/'prov-p2d-20261109/PCUD_EQ_STATUS.json'))['modules']
    for m,v in d.items():
        out.setdefault(m,{})
        for n,r in v['reached'].items(): out[m].setdefault(n,(r['status'],'P2d',None))
    return out
SD=status_defs()
def variants(rel):
    v=[rel]
    if rel.startswith('aspis_core.'): v.append(rel[len('aspis_core.'):])
    else: v.append('aspis_core.'+rel)
    return v
if __name__=='__main__':
    P=json.load(open(EV/'prov-p2d-20261109/PCUD_PARTITION.json'))['modules']
    tot=collections.Counter();res={}
    for m,defs in SD.items():
        ns=None
        hits=collections.defaultdict(dict)
        for full,(st,src,_) in defs.items():
            for e,ent in idx.items():
                for kind in ('Types','Funs'):
                    names=ent.get(kind,{})
                    for rel in set(full.split('.',1)[1:] ) :
                        pass
        res[m]=hits
    # gate namespace = module minus trailing .Funs/.Types in most cases: derive from definition names by longest common prefix handled below
    for m,defs in SD.items():
        gns=None
        # find namespace: for P2a/P2d first segment
        for full in defs:
            gns=full.split('.')[0];break
        hit=collections.defaultdict(list);unm=[]
        for full,(st,src,_) in defs.items():
            rel=full[len(gns)+1:] if full.startswith(gns+'.') else full
            found=False
            for e,ent in idx.items():
                for kind in ('Types','Funs'):
                    for vname in variants(rel):
                        if vname in ent.get(kind,{}):
                            hit[ent['run']].append((full,kind,vname,st));found=True
            if not found: unm.append((full,st))
        tot['modules']+=1
        print(m,'| defs',len(defs),'| matched',sum(len({x[0] for x in v}) for v in hit.values()),{k:len(v) for k,v in hit.items()})
