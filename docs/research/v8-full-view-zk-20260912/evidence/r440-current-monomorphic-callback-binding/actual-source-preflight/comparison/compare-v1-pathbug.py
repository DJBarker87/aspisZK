#!/usr/bin/env python3
"""Lossless hashcons expansion and literal R437/R440 LLBC structural diff."""
import hashlib,json
from pathlib import Path
ROOT=Path.cwd(); OUT=ROOT/'.r21-scratch/r440-mono-closure-binding/actual-source-preflight/comparison'
INPUTS={
 'R437':ROOT/'.r21-scratch/r437-pointer-source-boundary/root-launch-a/saved-output/R437PointerWrapperLayout.llbc',
 'R440':ROOT/'.r21-scratch/r440-mono-closure-binding/actual-source-preflight/lead-launch-a/saved-output/R440ActualMonoClosure.llbc'}
PINS={'R437':'bafe9c1297a8ea92eaea3c37c685da3f5d3fe2e04c335ac9f1f4d64c4312386c','R440':'01cd5ddc7086bba5f4e92802f90e59cce4034cf519d495ec35f925b91a6f033d'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def capture(k,p):
 assert sha(p)==PINS[k],(k,sha(p),PINS[k])
 doc=json.loads(p.read_text()); assert doc['has_errors'] is False
 tr=doc['translated']; defs={}
 def collect(x):
  if isinstance(x,dict):
   h=x.get('HashConsedValue')
   if isinstance(h,list) and len(h)==2:
    i,v=h
    if i in defs and defs[i]!=v:raise ValueError(f'{k}: hashcons collision {i}')
    defs[i]=v
   for v in x.values():collect(v)
  elif isinstance(x,list):
   for v in x:collect(v)
 collect(tr)
 def expand(x,stack=()):
  if isinstance(x,dict):
   if set(x)=={'HashConsedValue'}:
    i=x['HashConsedValue'][0]
    if i in stack:raise ValueError(f'{k}: hashcons cycle {i}')
    return expand(defs[i],stack+(i,))
   if set(x)=={'Deduplicated'}:
    i=x['Deduplicated']
    if i in stack:raise ValueError(f'{k}: dedup cycle {i}')
    return expand(defs[i],stack+(i,))
   return {a:expand(b,stack) for a,b in x.items()}
  if isinstance(x,list):return [expand(v,stack) for v in x]
  return x
 expanded=expand(tr)
 return doc,expanded,len(defs)
A={k:capture(k,p) for k,p in INPUTS.items()}
for k,(doc,tr,n) in A.items():
 (OUT/f'{k.lower()}-expanded.json').write_text(json.dumps({'charon_version':doc.get('charon_version'),'has_errors':doc['has_errors'],'translated':tr},sort_keys=True,separators=(',',':'))+'\n')

def diff(a,b,path=()):
 out=[]
 if type(a) is not type(b):return [{'path':list(path),'kind':'type','left_type':type(a).__name__,'right_type':type(b).__name__,'left':a,'right':b}]
 if isinstance(a,dict):
  for k in sorted(set(a)|set(b)):
   if k not in a:out.append({'path':list(path+[k]),'kind':'missing_left','right':b[k]})
   elif k not in b:out.append({'path':list(path+[k]),'kind':'missing_right','left':a[k]})
   else:out.extend(diff(a[k],b[k],path+(k,)))
 elif isinstance(a,list):
  if len(a)!=len(b):out.append({'path':list(path),'kind':'length','left':len(a),'right':len(b)})
  for i in range(min(len(a),len(b))):out.extend(diff(a[i],b[i],path+(i,)))
 elif a!=b:out.append({'path':list(path),'kind':'value','left':a,'right':b})
 return out
left={'charon_version':A['R437'][0].get('charon_version'),'has_errors':A['R437'][0]['has_errors'],'translated':A['R437'][1]}
right={'charon_version':A['R440'][0].get('charon_version'),'has_errors':A['R440'][0]['has_errors'],'translated':A['R440'][1]}
diffs=diff(left,right)
(OUT/'literal-expanded-diff.json').write_text(json.dumps({'status':'exhaustive literal structural diff; no fields normalized','R437_sha256':PINS['R437'],'R440_sha256':PINS['R440'],'diff_count':len(diffs),'diffs':diffs},indent=2,sort_keys=True)+'\n')
from collections import Counter
counts=Counter(tuple(d['path'][:3]) for d in diffs)
summary={'R437_sha256':PINS['R437'],'R440_sha256':PINS['R440'],'hashcons_entries':{k:v[2] for k,v in A.items()},'diff_count':len(diffs),'top_path_counts':{json.dumps(k):v for k,v in counts.most_common(80)},'top_level_keys':{k:len(A[k][1]) if isinstance(A[k][1],(list,dict)) else None for k in A},'has_errors':{k:A[k][0]['has_errors'] for k in A}}
(OUT/'literal-diff-summary.json').write_text(json.dumps(summary,indent=2,sort_keys=True)+'\n')
print(json.dumps(summary,indent=2,sort_keys=True))
