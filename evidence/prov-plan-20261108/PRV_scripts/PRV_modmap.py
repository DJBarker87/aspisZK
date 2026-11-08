import json,collections,sys
S=sys.argv[1]
idx=json.load(open(f"{S}/lean_index.json"))
scan={}
for l in open("ledger27-20261111/NNK_LOADED_scan.jsonl"):
    r=json.loads(l); scan[r['module']]=r
lib=('Init','Std','Lean','Mathlib','Aeneas','Batteries','Qq','Aesop','ProofWidgets','Plausible','LeanSearchClient','ImportGraph','Lake')
proj={m:r for m,r in scan.items() if m.split('.')[0] not in lib}
bymod=collections.defaultdict(set)
byimp=collections.defaultdict(set)
for gid,v in idx.items():
    for p in v['paths']:
        parts=p[:-5].split('/')
        for i in range(len(parts)): bymod['.'.join(parts[i:])].add(gid)
    byimp[tuple(v['imports'])].add(gid)
res={}; stat=collections.Counter()
for m,r in proj.items():
    oi=tuple(sorted(set(r['imports'])))
    named=bymod.get(m,set())
    match=[g for g in named if tuple(idx[g]['imports'])==oi]
    shas=sorted(set(idx[g]['sha256'] for g in match))
    how='path+imports' if shas else None
    if not shas:
        other=[g for g in byimp.get(oi,()) ]
        how='imports-only' if other else 'none'
        shas_other=sorted(set(idx[g]['sha256'] for g in other))
    else: shas_other=[]
    em=any(idx[g]['aeneas_header'] or idx[g]['rust_annotations'] for g in match)
    res[m]={'how':how,'candidates':shas,'n_named':len(set(idx[g]['sha256'] for g in named)),'emitted_candidate':em,
            'imports_only_candidates':len(shas_other),'decls':r['declarations']}
    stat[(how, 'multi' if len(shas)>1 else 'single' if shas else '-', em)]+=1
json.dump(res,open(f"{S}/proj_modmap.json","w"))
for k,n in sorted(stat.items(),key=lambda x:-x[1]): print(n,k)
