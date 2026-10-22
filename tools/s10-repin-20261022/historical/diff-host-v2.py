#!/usr/bin/env python3
"""Exhaustive compiler/body/instance/edge deltas; do not infer semantics."""
import collections,hashlib,json,re,struct
from pathlib import Path
H=Path('/home/dombarker/project-offloads/codex-cx-s10-repin-20261022')
P=H.parent/'codex-cx-s10-inventory3-20261021'
F=H.parent/'codex-cx-s10-inventory-20261021'
sha=lambda b:hashlib.sha256(b).hexdigest()
def dump(name,x):
 p=H/name;p.write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
 print(name,p.stat().st_size,flush=True)
def normalize(s):
 # Only source coordinates and absolute workspace prefixes are erased.
 s=re.sub(r'/home/dombarker/project-offloads/[^/]+/src/','WORKSPACE/',s)
 return re.sub(r'([\w./-]+\.rs):\d+:\d+(?:: \d+:\d+)?',r'\1:SPAN',s)
def functions(d):
 rows=[]
 for p in sorted((d/'compiler-output').glob('*.mir')):
  lines=p.read_text().splitlines(keepends=True);i=0
  while i<len(lines):
   if not lines[i].startswith('fn '):i+=1;continue
   start=i;i+=1
   while i<len(lines) and lines[i].rstrip('\n')!='}':i+=1
   body=''.join(lines[start:i+1]);header=lines[start].rstrip();crate=p.stem.split('-')[0]
   rows.append(dict(key=crate+':'+normalize(header),crate=crate,path=str(p),line=start+1,header=header,
    sha256=sha(body.encode()),normalized_sha256=sha(normalize(body).encode()),
    inline_scopes=[l.strip() for l in body.splitlines() if '(inlined ' in l],
    calls=[l.strip() for l in body.splitlines() if ' -> ' in l and '=' in l],body=body))
   i+=1
 return rows
def group(rows):
 out=collections.defaultdict(list)
 for r in rows:out[r['key']].append(r)
 return out
def short(r):return {k:v for k,v in r.items() if k!='body'}
def mono(d):
 c=collections.Counter()
 for p in sorted((d/'diagnostics').glob('*.mono.txt')):
  for l in p.read_text().splitlines():c[normalize(l)]+=1
 return c
def mono_exact(d):
 return collections.Counter(l for p in sorted((d/'diagnostics').glob('*.mono.txt')) for l in p.read_text().splitlines())
def llvm(d):
 rows=[]
 for p in sorted((d/'compiler-output').glob('*.ll')):
  lines=p.read_text().splitlines();i=0
  while i<len(lines):
   l=lines[i]
   if not l.startswith(('define ','declare ')):i+=1;continue
   start=i;declaration=l.startswith('declare ')
   if not declaration:
    while lines[i]!='}':i+=1
   body='\n'.join(lines[start:i+1])+'\n'
   m=re.search(r'@(?:"([^"]+)"|([^ (]+))\(',l);assert m,l
   symbol=m[1] or m[2]
   calls=re.findall(r'\b(?:call|invoke)\b.*?@(?:"([^"]+)"|([^ (]+))\(',body)
   rows.append(dict(key=p.stem.split('-')[0]+':'+symbol,raw_symbol=symbol,path=str(p),line=start+1,
    kind='declaration' if declaration else 'definition',sha256=sha(body.encode()),calls=[a or b for a,b in calls]))
   i+=1
 return rows
def delta(a,b):
 return [dict(item=k,old=a[k],new=b[k]) for k in sorted(a.keys()|b.keys()) if a[k]!=b[k]]
oldelf=json.loads((F/'collected/elf-graphs.json').read_text())['artifacts']
newelf=json.loads((H/'collected/elf-graphs.json').read_text())['artifacts']
mir=[];instances={};elf={};allnew=[];exact={};llvmdiffs={}
for mode,oldbuild,newbuild in [('default','build-default-v3','build-default-v2'),('devnet','build-devnet-v1','build-devnet-v1'),('pool','build-pool-v1','build-pool-v1')]:
 a=functions(P/oldbuild);b=functions(H/newbuild);ga=group(a);gb=group(b)
 allnew.extend(dict(mode=mode,**short(r)) for r in b)
 changed=[];same=0;locations=[]
 for k in sorted(ga.keys()|gb.keys()):
  aa=ga[k];bb=gb[k]
  x=collections.Counter(r['normalized_sha256'] for r in aa);y=collections.Counter(r['normalized_sha256'] for r in bb)
  if x==y:
   same+=len(bb)
   if collections.Counter(r['sha256'] for r in aa)!=collections.Counter(r['sha256'] for r in bb):locations.append(k)
   continue
  # Never silently choose one duplicate declaration signature.
  changed.append(dict(key=k,old=[short(r) for r in aa],new=[short(r) for r in bb],
   call_edge_changes=delta(collections.Counter(normalize(c) for r in aa for c in r['calls']),collections.Counter(normalize(c) for r in bb for c in r['calls'])),
   status='ADDED' if not aa else 'REMOVED' if not bb else 'BODY_CHANGED',
   ambiguous_signature=len(aa)>1 or len(bb)>1))
 mir.append(dict(mode=mode,old_functions=len(a),new_functions=len(b),unchanged_after_coordinate_normalization=same,
  coordinate_only_changes=locations,changed=changed))
 instances[mode]=delta(mono(P/oldbuild),mono(H/newbuild))
 exact[mode]=delta(mono_exact(P/oldbuild),mono_exact(H/newbuild))
 la=group(llvm(P/oldbuild));lb=group(llvm(H/newbuild));lchanges=[]
 for k in sorted(la.keys()|lb.keys()):
  aa=la[k];bb=lb[k]
  if collections.Counter(r['sha256'] for r in aa)==collections.Counter(r['sha256'] for r in bb):continue
  lchanges.append(dict(key=k,old=aa,new=bb,
   call_edge_changes=delta(collections.Counter(c for r in aa for c in r['calls']),collections.Counter(c for r in bb for c in r['calls'])),
   status='ADDED' if not aa else 'REMOVED' if not bb else 'EMITTED_TEXT_CHANGED'))
 llvmdiffs[mode]=lchanges
 def graph(g):
  raw=Path(g['linked']['path']).read_bytes();h=struct.unpack_from('<16sHHIQQQIHHHHHH',raw)
  sections=[struct.unpack_from('<IIQQQQIIQQ',raw,h[6]+i*h[11]) for i in range(h[12])]
  # All instruction symbols reside in the same executable text section.
  text=next(s for s in sections if s[2]&4 and s[5])
  names={s['address']:s['name'] for s in g['symbols']};syms={s['name']:s for s in g['symbols']}
  syms={k:dict(s,body_sha256=sha(raw[text[4]+s['address']-text[3]:text[4]+s['address']-text[3]+s['size']])) for k,s in syms.items()}
  edges=collections.Counter()
  for c in g['calls']:
   target=names.get(c['target'],c['target']) if c['kind']=='direct' else c['target']
   edges[(names[c['caller']],c['kind'],str(target))]+=1
  return syms,edges
 os,oe=graph(oldelf[mode]);ns,ne=graph(newelf[mode]);symbolchanges=[]
 for k in sorted(os.keys()|ns.keys()):
  if os.get(k)!=ns.get(k):symbolchanges.append(dict(name=k,old=os.get(k),new=ns.get(k),
   status='ADDED' if k not in os else 'REMOVED' if k not in ns else 'LAYOUT_OR_SIZE_CHANGED'))
 elf[mode]=dict(symbol_changes=symbolchanges,edge_changes=delta(oe,ne),
  old_direct_reachable=[osn for osn,s in os.items() if s['address'] in oldelf[mode]['direct_reachable']],
  new_direct_reachable=[nsn for nsn,s in ns.items() if s['address'] in newelf[mode]['direct_reachable']],
  old_calls=len(oldelf[mode]['calls']),new_calls=len(newelf[mode]['calls']))
dump('mir-diff.json',dict(schema='s10-adopted-mir-diff-v1',modes=mir,
 normalization='Absolute workspace prefix and Rust source coordinates only. Full raw body hashes retained. Unmatched/duplicate signatures retained, never guessed.'))
dump('mono-diff.json',instances)
dump('mono-exact-diff.json',exact)
dump('llvm-diff.json',dict(modes=llvmdiffs,scope='Every changed emitted LLVM definition/declaration multiset, raw symbol, full text hash and direct call-edge multiset; metadata/layout changes are included. An emitted function need not survive final linking.'))
dump('elf-diff.json',elf)
dump('mir-declarations.json',dict(schema='s10-adopted-frozen-mir-declarations-v1',records=allnew,
 scope='Emitted generic source bodies with inline scopes and call operands; not a complete deployed reachable instance inventory.'))
print(json.dumps(dict(mir=[dict(mode=r['mode'],changed=len(r['changed']),old=r['old_functions'],new=r['new_functions']) for r in mir],mono={m:len(v) for m,v in instances.items()},elf={m:dict(symbols=len(v['symbol_changes']),edges=len(v['edge_changes'])) for m,v in elf.items()})))
