#!/usr/bin/env python3
"""NPH_ T1 host census (read-only over the L187 replayed closure sources).
For every definition in PCXD_R22_SPLIT.json (checked, mixed, wrapping classes) locate its
`def` in the replay src tree, extract the body text, its Aeneas `Source:` annotation, and a
normalised body hash (module namespace prefix removed) so copies can be grouped.
Usage: python3 NPH_census_host.py SPLIT.json SRC_ROOT OUT.json"""
import json,sys,re,hashlib,pathlib
split=json.load(open(sys.argv[1]));src=pathlib.Path(sys.argv[2])
def modfile(m):
  p=src/(m.replace('.','/')+'.lean')
  return p if p.exists() else None
cache={}
def defs_of(p):
  if p in cache: return cache[p]
  t=p.read_text(); lines=t.split('\n'); ns=[]; out={}
  starts=[]
  for i,l in enumerate(lines):
    m=re.match(r'^namespace\s+(\S+)',l)
    if m: ns.append(m.group(1))
    m=re.match(r'^end\s+(\S+)',l)
    if m and ns and ns[-1]==m.group(1): ns.pop()
    m=re.match(r'^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+|private\s+|partial\s+)*(def|abbrev|structure|inductive|opaque|axiom)\s+(\S+)',l)
    if m: starts.append((i,'.'.join(ns+[m.group(2)]),m.group(1),'.'.join(ns)))
  for k,(i,name,kind,nsn) in enumerate(starts):
    j=starts[k+1][0] if k+1<len(starts) else len(lines)
    # trim trailing doc comment of next def
    body=lines[i:j]
    while body and (body[-1].strip()=='' or body[-1].startswith('/--') or body[-1].strip().startswith('Source:') or body[-1].strip().startswith('Visibility:') or body[-1].strip().endswith('-/')):
      body=body[:-1]
    # source annotation: look back from i for 'Source:'
    srcl=None
    for b in range(i-1,max(-1,i-6),-1):
      mm=re.search(r"Source: '([^']+)', lines (\S+)",lines[b])
      if mm: srcl=(mm.group(1),mm.group(2));break
    text='\n'.join(body)
    norm=text.replace(nsn+'.','') if nsn else text
    out[name]=dict(line=i+1,kind=kind,namespace=nsn,source=srcl,text=text,norm_sha=hashlib.sha256(norm.encode()).hexdigest()[:16])
  cache[p]=out;return out
res=[]
for cls,L in split['definitions'].items():
  if cls=='configuration_independent_no_arithmetic_in_body': continue
  for x in L:
    p=modfile(x['module']);r=dict(x,cls=cls,file=str(p.relative_to(src)) if p else None)
    if p:
      d=defs_of(p);hit=d.get(x['definition'])
      if hit is None and x['definition'].endswith('.body'):
        hit=d.get(x['definition'][:-5]); r['located_as']='loop parent' if hit else None
      if hit: r.update(line=hit['line'],kind=hit['kind'],rust_source=hit['source'],norm_sha=hit['norm_sha'],text=hit['text'][:4000])
    res.append(r)
json.dump(res,open(sys.argv[3],'w'),indent=1)
print(len(res),sum(1 for r in res if r.get('line')))
