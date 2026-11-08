import json,re,collections,sys
S=sys.argv[1]
scan={}
for l in open("ledger27-20261111/NNK_LOADED_scan.jsonl"):
    r=json.loads(l); scan[r['module']]=r
bm=json.load(open(f"{S}/blob_mods.json"))
def imports(t):
    out=[];prelude=False
    t=re.sub(r'/-.*?-/','',t,flags=re.S)
    for line in t.splitlines():
        s=line.split('--')[0].strip()
        if not s: continue
        if s=='prelude': prelude=True; continue
        if s.startswith('import '): out+=s[7:].split(); continue
        break
    if not prelude: out.append('Init')
    return sorted(set(out))
bym=collections.defaultdict(list)
for b,ms in bm.items():
    m=ms[0]; t=open(f"{S}/blobs/{b}.lean").read()
    bym[m].append((b,imports(t)==sorted(set(scan[m]['imports'])),imports(t)))
out={}
for m,L in bym.items():
    out[m]={'olean_imports':sorted(set(scan[m]['imports'])),'olean_decls':scan[m]['declarations'],'versions':[{'blob':b,'imports_match':ok,'imports':i} for b,ok,i in L]}
json.dump(out,open(f"{S}/modver.json","w"),indent=1)
c=collections.Counter()
for m,v in out.items():
    k=sum(x['imports_match'] for x in v['versions']); c[(len(v['versions'])>1,k)]+=1
    if k!=1: print(m,len(v['versions']),k, v['olean_imports'], [x['imports'] for x in v['versions'] if not x['imports_match']][:2])
print(c)
