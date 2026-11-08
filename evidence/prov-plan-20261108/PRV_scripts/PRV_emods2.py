import json,collections,sys,subprocess,re,lzma
from multiprocessing import Pool
sys.path.insert(0,'emission-repro-20261110'); sys.path.insert(0,sys.argv[1])
from NMH_names import uncomment
S=sys.argv[1]
exec(open(f"{S}/decls.py").read().split("modver=json.load")[0].split("S=sys.argv[1]")[1])  # defines rx, decls
idx=json.load(open(f"{S}/lean_index.json"))
sha2gid={}
for g,v in idx.items(): sha2gid.setdefault(v['sha256'],g)
emods=json.load(open(f"{S}/emods.json"))
def cat(g): return subprocess.run(['git','cat-file','-p',g],capture_output=True).stdout.decode('utf-8','replace')
for m,v in emods.items():
    sets=[]
    allnames=set()
    for s in v['candidates']:
        try: d=decls(cat(sha2gid[s]))
        except AssertionError: d=[]
        ns=set(n for n,k in d); sets.append(ns); allnames|=ns
    v['strong_names']=sorted(set.intersection(*sets)) if sets else []
    v['any_names']=sorted(allnames)
json.dump(emods,open(f"{S}/emods_decl.json","w"))
n2=collections.defaultdict(set)
for m,v in emods.items():
    for n in v['strong_names']: n2[n].add(m)
names=set(n2)
roots=json.load(open(f"{S}/roots.json")); rf=json.load(open(f"{S}/rootfile.json"))
privrx=re.compile(r'^_private\.(.+?)\.0\.(.+)$')
def work(root):
    f="ledger27-20261111/"+rf[root][0]
    hit=collections.defaultdict(set)
    for line in lzma.open(f,'rt'):
        n=line.strip()
        if not n: continue
        pm=privrx.match(n)
        if pm:
            if pm[1] in emods: hit[pm[1]].add(pm[2])
            n=pm[2]
        if n in names:
            for m in n2[n]: hit[m].add(n)
            continue
        parts=n.split('.')
        for i in range(len(parts)-1,1,-1):
            p='.'.join(parts[:i])
            if p in names:
                for m in n2[p]: hit[m].add(p)
                break
    return root,{k:sorted(v) for k,v in hit.items()}
if __name__=='__main__':
    with Pool(8) as p: out=dict(p.map(work,sorted(roots),chunksize=4))
    json.dump(out,open(f"{S}/emod_hits.json","w"))
    rel=collections.defaultdict(set); defs=collections.defaultdict(set)
    for r,h in out.items():
        for m,ns in h.items(): rel[m].add(r); defs[m]|=set(ns)
    print("emitted modules relied:",len(rel),"of",len(emods))
    rows=set(x for m in rel for r in rel[m] for x in roots[r]); print("rows relying on any emitted module:",len(rows))
    print("distinct reached emitted names:",sum(len(v) for v in defs.values()))
