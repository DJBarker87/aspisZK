import json,collections,sys,subprocess,re
sys.path.insert(0,'emission-repro-20261110')
from NMH_names import uncomment
S=sys.argv[1]
idx=json.load(open(f"{S}/lean_index.json"))
sha2gid={}
for g,v in idx.items(): sha2gid.setdefault(v['sha256'],g)
mm=json.load(open(f"{S}/proj_modmap.json"))
scan={}
for l in open("ledger27-20261111/NNK_LOADED_scan.jsonl"):
    r=json.loads(l); scan[r['module']]=r
byimp=collections.defaultdict(list)
for g,v in idx.items():
    if v['aeneas_header'] or v['rust_annotations']: byimp[tuple(v['imports'])].append(g)
def cat(g): return subprocess.run(['git','cat-file','-p',g],capture_output=True).stdout.decode('utf-8','replace')
emods={}
for m,v in mm.items():
    if v['how']=='path+imports':
        if v['emitted_candidate']:
            cands=[s for s in v['candidates'] if idx[sha2gid[s]]['aeneas_header'] or idx[sha2gid[s]]['rust_annotations']]
            emods[m]={'resolution':'path+imports','candidates':cands,'nonemitted_candidates':[s for s in v['candidates'] if s not in cands]}
    else:
        oi=tuple(sorted(set(scan[m]['imports']))); ns=m.split('.')[0]
        good=set()
        for g in byimp.get(oi,[]):
            t=cat(g)
            if re.search(r'(?m)^namespace '+re.escape(ns)+r'(\.|\s|$)',t): good.add(idx[g]['sha256'])
        if good: emods[m]={'resolution':'imports+namespace(renamed source)','candidates':sorted(good),'nonemitted_candidates':[]}
print(len(emods), collections.Counter(v['resolution'] for v in emods.values()))
json.dump(emods,open(f"{S}/emods.json","w"),indent=0)
