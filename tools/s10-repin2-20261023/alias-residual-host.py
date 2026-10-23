#!/usr/bin/env python3
"""Retain exact text residuals after alias comparison; no proof by naming."""
import collections,difflib,hashlib,json
from pathlib import Path
H=Path('/home/dombarker/project-offloads/codex-cx-s10-repin2-20261023');P=H.parent/'codex-cx-s10-repin-20261022'
ns={};exec((H/'alias-mir-host.py').read_text().split('out=[]')[0],ns)
out=[]
for mode,old,new in [('default','build-default-v2','build-default-v3'),('devnet','build-devnet-v1','build-devnet-v2')]:
 a=ns['ns']['functions'](P/old);b=ns['ns']['functions'](H/new);canonical=ns['canonical']
 def group(rows):
  g=collections.defaultdict(list)
  for r in rows:g[r['crate']+':'+canonical(r['header'])].append(r)
  return g
 aa=group(a);bb=group(b)
 for k in sorted(aa.keys()&bb.keys()):
  if len(aa[k])!=1 or len(bb[k])!=1:continue
  left=canonical(aa[k][0]['body']);right=canonical(bb[k][0]['body'])
  if left==right:continue
  out.append(dict(mode=mode,key=k,unified_diff='\n'.join(difflib.unified_diff(left.splitlines(),right.splitlines(),n=1))))
(H/'alias-residuals.json').write_text(json.dumps(out,indent=2)+'\n')
print(len(out))
