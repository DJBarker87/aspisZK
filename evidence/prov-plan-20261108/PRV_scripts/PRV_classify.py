import json,collections,sys,subprocess,re
S=sys.argv[1]; sys.path.insert(0,S)
from defseg import segments
idx=json.load(open(f"{S}/lean_index.json"))
sha2gid={}; sha2paths=collections.defaultdict(set)
for g,v in idx.items(): sha2gid.setdefault(v['sha256'],g); sha2paths[v['sha256']]|=set(v['paths'])
def cat_sha(s): return subprocess.run(['git','cat-file','-p',sha2gid[s]],capture_output=True).stdout.decode('utf-8','replace')
em=json.load(open(f"{S}/emods_decl.json")); hits=json.load(open(f"{S}/emod_hits.json")); roots=json.load(open(f"{S}/roots.json"))
ext={e['emitted_file_sha256']:e['origin_status'] for e in json.load(open("emission-audit-20261109/NKT_EXTRACTIONS.json"))}
nmlp={b['blob']:b for b in json.load(open("emission-repro2-20261110/NML_PROVENANCE.json"))['blobs']}
nmlin={b['blob']:b['source_status'] for b in json.load(open("emission-repro2-20261110/NML_INPUT_MAP.json"))['blobs']}
inv={b['blob']:b for b in json.load(open("emission-repro-20261110/NMH_INVENTORY.json"))['blobs']}
outs=json.load(open(f"{S}/outside_strict.json"))
sp=json.load(open(f"{S}/strictpins_hashes.json"))
frozen_hashes=set(); any_pin_hashes=set()
for p,v in sp.items():
    any_pin_hashes|=set(v['hashes'])
    if v['frozen']: frozen_hashes|=set(v['hashes'])
# fresh frozen emitted lean files
F=collections.defaultdict(set); Fsrc=collections.defaultdict(set)
fresh_files=[s for s in sha2gid if s in frozen_hashes and (idx[sha2gid[s]]['aeneas_header'] or idx[sha2gid[s]]['rust_annotations'])]
for s in fresh_files:
    for seg in segments(cat_sha(s)):
        F[seg['symn']].add(seg['norm_sha']); Fsrc[seg['symn']].add(s)
print("fresh frozen emitted files",len(fresh_files),"symbols",len(F))
def cand_status(s):
    if s in nmlp and nmlp[s]['verdict'].startswith('REPRODUCED'): return 'REPRODUCED'
    if s in ext and ext[s]=='HASH_LINKED_PIN_RECEIPT': return 'RECEIPTED'
    if s in inv: return 'UNRECEIPTED_INV336'
    if s in outs and outs[s]['strict_receipts']: return 'RECEIPTED'
    if s in any_pin_hashes: return 'RECEIPTED'
    return 'UNRECEIPTED_OUTSIDE'
rel=collections.defaultdict(set); reached=collections.defaultdict(set)
for r,h in hits.items():
    for m,ns in h.items(): rel[m].add(r); reached[m]|=set(ns)
REFRX=re.compile(r'(?i)(ref(erence)?$|_ref$|reference|^n[a-z]{2}_|kit)')
FROZEN_CRATES={'aspis_core','aspis_statement','aspis_r1_cost_probe','aspis_r1_cost_probe_program','aspis_pool','r1_cost_probe'}
out={}
for m,v in em.items():
    cs=v['candidates']; sts=[cand_status(s) for s in cs]
    texts={s:cat_sha(s) for s in cs}
    crates=set()
    for s,t in texts.items():
        mm=re.search(r'^-- \[([A-Za-z0-9_]+)\]',t,re.M)
        if mm: crates.add(mm.group(1))
    ns=m.split('.')[0]
    is_ref=any(REFRX.search(c) for c in crates) or bool(re.search(r'(Ref|Reference)(\b|_|$)',m))
    if crates & FROZEN_CRATES and not is_ref: kind='FROZEN_CRATE'
    elif is_ref: kind='REFERENCE'
    elif crates: kind='PROBE_OR_CUT_CRATE'
    else: kind='TRANSFORMED_COPY'
    # reached defs -> segments
    segs_by_cand={}
    for s,t in texts.items():
        nsm=re.search(r'(?m)^namespace (\S+)',t); nsp=nsm.group(1) if nsm else ''
        L=[]
        for seg in segments(t):
            hm=re.search(r'\b(?:def|abbrev|structure|inductive|opaque|axiom|theorem|instance)\s+(\S+)',seg['head'])
            seg['lean']=(nsp+'.' if nsp else '')+hm.group(1) if hm else None
            L.append(seg)
        segs_by_cand[s]=L
    rset=reached.get(m,set())
    defs={}
    for s,L in segs_by_cand.items():
        for seg in L:
            if seg['lean'] in rset or any(x.startswith((seg['lean'] or '#')+'.') for x in ()):
                d=defs.setdefault(seg['lean'],{'symn':seg['symn'],'src':seg['src'],'shas':set()})
                d['shas'].add(seg['norm_sha'])
    cover=collections.Counter()
    for n,d in defs.items():
        if d['symn'] not in F: d['cov']='UNCOVERED'
        elif d['shas']<=F[d['symn']]: d['cov']='IDENTICAL'
        elif d['shas']&F[d['symn']]: d['cov']='IDENTICAL_SOME_VERSION'
        else: d['cov']='COVERED_DIFFERS'
        cover[d['cov']]+=1
    out[m]={'kind':kind,'crates':sorted(crates),'candidates':[{'sha256':s,'status':st,'paths':sorted(sha2paths[s])[:3],'nml_source_status':nmlin.get(s)} for s,st in zip(cs,sts)],
            'relied':m in rel,'roots':sorted(rel.get(m,())),'rows':sorted(set(x for r in rel.get(m,()) for x in roots[r])),
            'reached_names':len(rset),'reached_emitted_defs':len(defs),'coverage':dict(cover),
            'defs':{n:{'symn':d['symn'],'src':d['src'],'cov':d['cov']} for n,d in defs.items()}}
json.dump(out,open(f"{S}/classified.json","w"),indent=0)
c=collections.Counter()
for m,o in out.items():
    st=set(x['status'] for x in o['candidates'])
    stat='RECEIPTED' if st<= {'RECEIPTED','REPRODUCED'} else ('MIXED' if st&{'RECEIPTED','REPRODUCED'} else 'UNRECEIPTED')
    o['prov']=stat
    c[(o['relied'],stat,o['kind'])]+=1
json.dump(out,open(f"{S}/classified.json","w"),indent=0)
for k,n in sorted(c.items(),key=lambda x:(-x[0][0],-x[1])): print(n,k)
