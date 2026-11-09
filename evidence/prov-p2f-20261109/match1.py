import json,collections,sys
sys.dont_write_bytecode=True
EV='..'
idx=json.load(open('PCUF_EMISSION_INDEX.json'))
def variants(rel):
    v=[rel]
    v.append(rel[len('aspis_core.'):] if rel.startswith('aspis_core.') else 'aspis_core.'+rel)
    return v
recs=[]
for f,tool in [("prov-p2r-20261109/PCUE_EQ_STATUS.json","P2r"),("prov-p2b-20261109/PCUB_EQ_STATUS.json","P2b"),("prov-p2c-20261109/PCUC_EQ_STATUS.json","P2c")]:
    d=json.load(open(f"{EV}/{f}"))["modules"]
    for m,v in d.items():
        for n,r in v["reached"].items(): recs.append((tool,m,n,r["status"],r))
tot=collections.Counter();hits=collections.defaultdict(list)
for tool,m,n,s,r in recs:
    if s not in("NO_FRESH_EMISSION","FAILED","CONFIG_PENDING","GATE_SOURCE_UNAVAILABLE","NO_COMMON_LEAN_NAME","FRESH_EXTERNAL_AXIOM_ONLY","TEXT_ONLY_NOT_COMPARED","TEXT_IDENTICAL_ONLY","TEXT_DIFFERS"): continue
    rel=n.split('.',1)[1] if '.' in n else n
    found=[]
    for e,ent in idx.items():
        if not ent['eligible']: continue
        for k in('Types','Funs'):
            for v in variants(rel):
                nm=ent.get(k,{})
                if v in nm and nm[v] not in('axiom','opaque'): found.append((ent['run'],k,v,nm[v]))
    tot[(tool,s,bool(found))]+=1
    if found: hits[(tool,m)].append((n,s,found))
for k,v in sorted(tot.items()): print(v,k)
print()
for k,v in sorted(hits.items()): print(k,len(v),collections.Counter(x[1] for x in v), sorted({f[0] for x in v for f in x[2]}))
