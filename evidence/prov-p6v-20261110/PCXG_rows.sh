#!/bin/bash
# PCXG_rows.sh: PCXG_ROWS_ON_LEDGER30_VERSIONS.json. For each of the 599 ledger30 rows: does the import closure of its root-owner modules (ledger30 chain
# graph NNN_EXPECTED_IMPORTS.jsonl) load NHT_Constants or CurrentCompactCallerModelV1, and is any root constant in the L187 raw reachable lists
# (deployed_splitB, deployed_charge, NNH8_DeployedOuter). Import reach is an over-approximation of "the root cites the module".
cd "$(dirname "$0")/.."
python3 -I -B - <<'PY'
import json,lzma,sys,collections
sys.setrecursionlimit(100000)
L='ledger30-20261111/';V='replay-l187-20261109/final/'
g={}
for l in open(L+'NNN_EXPECTED_IMPORTS.jsonl'):
    x=json.loads(l); g[x['module']]=x['imports']
TG=['NHT_Constants','CurrentCompactCallerModelV1']
memo={}
def reach(m):
    if m in memo: return memo[m]
    memo[m]=frozenset(); s=set()
    for i in g.get(m,[]):
        if i in TG: s.add(i)
        s|=reach(i)
    memo[m]=frozenset(s); return memo[m]
def rd(p): return set(lzma.open(p).read().decode().split('\n'))
cone={'deployed_splitB':rd(V+'L187_AX2_splitB/audit/NEP_proof0_AspisR1.TAS_FinalB.deployed_splitB_REACHABLE.txt.xz'),
      'deployed_charge':rd(V+'L187_AX2_charge/audit/NEP_proof0_AspisR1.TAS_FinalB.deployed_charge_REACHABLE.txt.xz'),
      'NNH8_DeployedOuter':rd(V+'L187_AX2_outer/audit/NEP_proof0_AspisR1.NNH8_DeployedOuter_REACHABLE.txt.xz')}
d=json.load(lzma.open(L+'NNN_LEDGER.json.xz'))
rows=[];cnt=collections.Counter();incone=collections.Counter()
for r in d['rows']:
    roots=[]
    for o in r['root_owners']:
        m=o['owner_module'];hit=set(reach(m))|({m} & set(TG))
        inc=[k for k,s in cone.items() if o['root'] in s or ('AspisR1.'+o['root']) in s]
        roots.append(dict(root=o['root'],owner_module=m,loads_in_ledger30_chain=sorted(hit),in_L187_cones=inc))
    mods=sorted({h for x in roots for h in x['loads_in_ledger30_chain']})
    cone_roots=[x['root'] for x in roots if x['in_L187_cones']]
    rows.append(dict(row=r['row'],status=r['status'],function=r['function'],owner_module=r['owner_module'],loads_in_ledger30_chain=mods,n_roots=len(roots),roots_in_L187_cones=cone_roots,roots=roots))
    cnt[tuple(mods)]+=1
    if cone_roots: incone[tuple(mods)]+=1
summ={'|'.join(k) or 'neither':v for k,v in cnt.items()}
summ_cone={'|'.join(k) or 'neither':v for k,v in incone.items()}
nht=sorted(x for x in cone['deployed_splitB'] if x.startswith('NHT_Constants.') and '.eq_' not in x and '_proof' not in x)
out=dict(schema='PCXG_ROWS_ON_LEDGER30_VERSIONS/1',target_established=False,
 method='import-closure reach over the ledger30 chain graph (NNN_EXPECTED_IMPORTS.jsonl, 24,368 modules) from each row\'s root-owner modules to the two modules whose objects differ between the ledger30 chain and the L187 closure (PCXF_UNIVERSES.json); an over-approximation of "the root cites the module" (a root may import the module without using a declaration). The L187 lists (raw reachable lists of deployed_splitB, deployed_charge, NNH8_DeployedOuter) are authoritative for what the top theorems load.',
 n_rows=len(rows),rows_by_loaded_modules=summ,rows_with_a_root_in_an_L187_cone=sum(1 for r in rows if r['roots_in_L187_cones']),rows_with_a_root_in_an_L187_cone_by_loaded_modules=summ_cone,
 l187_cone_constants_from_NHT_Constants_in_deployed_splitB=len(nht),l187_cone_NHT_Constants_names=nht,
 l187_cone_constants_named_CurrentCompactCallerModelV1_in_deployed_splitB=sum(1 for x in cone['deployed_splitB'] if 'CurrentCompactCallerModelV1' in x),
 rows=rows)
json.dump(out,open('prov-p6v-20261110/PCXG_ROWS_ON_LEDGER30_VERSIONS.json','w'))
print({k:v for k,v in out.items() if k not in ('rows',)})
PY
