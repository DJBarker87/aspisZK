#!/usr/bin/env python3
"""Host side of stage 2: for each closure project module, find which candidate receipt output path
holds a byte-identical copy of the overlay object (object identity). stdin: {module: [[idx, out, base], ...]}"""
import json,sys,hashlib,os,collections
W='/home/dombarker/project-offloads/codex-cx-replay-l187-20261109'
q=json.load(sys.stdin); ov=json.load(open(W+'/overlay_sha.json'))
byname=collections.defaultdict(list)
for line in open(W+'/all_oleans.txt'):
  p=line.rstrip('\n'); byname[os.path.basename(p)].append(p)
cache={}
def h(p):
  if p not in cache:
    try: cache[p]=hashlib.sha256(open(p,'rb').read()).hexdigest()
    except Exception: cache[p]=None
  return cache[p]
res={}
for m,cands in q.items():
  hits=[]
  for idx,out,base in cands:
    paths=[os.path.join(base,out)] if base and not out.startswith('/') else ([out] if out.startswith('/') else [])
    if not paths or not os.path.isfile(paths[0]):
      paths=[p for p in byname.get(os.path.basename(out),[]) if p.endswith('/'+out.lstrip('./'))]
    for p in paths:
      if h(p)==ov[m]: hits.append([idx,p]); break
  res[m]=hits
print(json.dumps(res))
