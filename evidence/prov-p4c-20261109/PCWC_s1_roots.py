#!/usr/bin/env python3
"""PCWC_s1_roots.py: per-row reaching roots of S1ValuesOwnedModelV1 (AspisS1ValuesOwned.*), using PCO_partition stage_ledger root->REACHABLE choice."""
import json,re,subprocess,lzma,collections,sys
sys.dont_write_bytecode=True
REV='research'
led=json.load(open('/tmp/p4c_led.json'))
ROWS=['TX1:098','TX1:151','TX1:152','TX1:168','TX1:169','TX1:170','TX1:186']
paths=subprocess.check_output(['git','ls-tree','-r','--full-tree','--name-only',REV,'--','evidence'],text=True).splitlines()
RX=re.compile(r'^(?:.*/)?(?:[A-Za-z0-9]+_)??(?:FAILURE\d+_)?NEP_(?:proof\d+|fixtures)_(.+)_REACHABLE\.txt\.xz$')
cand=collections.defaultdict(list)
for p in paths:
    if p.endswith('REACHABLE.txt.xz'):
        m=RX.match(p)
        if m: cand[m.group(1)].append(p)
def order(p):
    m=re.search(r'ledger(\d+)-',p); return int(m.group(1)) if m else -1
out={'rows':{}, 'method':'PCO_partition.stage_ledger root->REACHABLE choice (newest ledger dir <= 30, no FAILURE), names matched by prefix AspisS1ValuesOwned.'}
byrow={r['row']:r for r in led['rows']}
cache={}
for row in ROWS:
    r=byrow[row]; res=[]
    for o in r['root_owners']:
        root=o['root']
        L=[p for p in cand.get(root,[]) if 'FAILURE' not in p.split('/')[-1] and order(p)<=30] or cand.get(root,[])
        L=sorted(L,key=lambda p:(-order(p),p))
        ent={'root':root,'owner_module':o['owner_module'],'reach_file':L[0] if L else None}
        if L:
            if L[0] not in cache:
                raw=subprocess.run(['git','cat-file','-p',f'{REV}:{L[0]}'],capture_output=True).stdout
                names=[x.strip() for x in lzma.decompress(raw).decode('utf-8','replace').splitlines() if x.strip()]
                cache[L[0]]=names
            names=cache[L[0]]
            hit=sorted(n for n in names if n.startswith('AspisS1ValuesOwned.') or n.startswith('_private.S1ValuesOwnedModelV1.') )
            ent['reachable_total']=len(names); ent['s1_owned_hits']=hit
        res.append(ent)
    out['rows'][row]={'status':r['status'],'roots':res}
json.dump(out,open('PCWC_S1_ROOTS.json','w'),indent=1)
for row,v in out['rows'].items():
    print(row,[(e['root'],len(e.get('s1_owned_hits',[])) if e['reach_file'] else 'NOFILE') for e in v['roots']])
