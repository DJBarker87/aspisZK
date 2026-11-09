#!/usr/bin/env python3
"""Module-level witness: BFS over NNN_LOADED_scan imports from each reaching root's owner module to S1ValuesOwnedModelV1; plus constant-level hit list from the reach file."""
import json,collections,sys
sys.dont_write_bytecode=True
imp={}
for l in open('../ledger30-20261111/NNN_LOADED_scan.jsonl'):
    r=json.loads(l); imp[r['module']]=r['imports']
d=json.load(open('PCWC_S1_ROOTS.json'))
T='S1ValuesOwnedModelV1'
def bfs(src):
    prev={src:None}; q=collections.deque([src])
    while q:
        m=q.popleft()
        if m==T:
            p=[]; 
            while m: p.append(m); m=prev[m]
            return p[::-1]
        for i in imp.get(m,[]):
            if i not in prev: prev[i]=m; q.append(i)
    return None
for row,v in d['rows'].items():
    for e in v['roots']:
        e['module_import_path']=bfs(e['owner_module']) if e['s1_owned_hits'] else None
        e['owner_module_in_scan']=e['owner_module'] in imp
        if e['s1_owned_hits'] and not e['module_import_path']: print('NOPATH',row,e['root'])
        # also: roots that do NOT reach by constants but reach by import?
        e['import_reaches_module']=bfs(e['owner_module']) is not None
json.dump(d,open('PCWC_S1_ROOTS.json','w'),indent=1)
for row,v in d['rows'].items():
    for e in v['roots']:
        print(row,e['root'],bool(e['s1_owned_hits']),e['import_reaches_module'],len(e['module_import_path'] or []))
