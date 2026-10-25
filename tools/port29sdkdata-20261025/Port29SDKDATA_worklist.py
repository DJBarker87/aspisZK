#!/usr/bin/env python3
"""Bounded noncompiler index/closure and incremental requests, while Lean waits."""
import collections, hashlib, json, os, resource, sqlite3, sys, time
from pathlib import Path
from Port29SDKDATA_diagnostic import E, OLD, CURRENT, pin, write
start=time.monotonic()
out=Path(sys.argv[1])
while not (out/'Port29SDKDATA_index-ready').exists():time.sleep(.1)
db=sqlite3.connect(out/'Port29SDKDATA_complete-index.sqlite')
db.executescript('PRAGMA journal_mode=OFF; PRAGMA cache_size=-16000; PRAGMA temp_store=FILE; PRAGMA mmap_size=0; CREATE TABLE decl(name TEXT,side TEXT,origin TEXT,module TEXT,path TEXT,part INTEGER,info TEXT);')
parts=[];comparisons=[];count=0;kinds=collections.Counter();safety=collections.Counter()
with (out/'Port29SDKDATA_raw.jsonl').open() as f:
 for line in f:
  row=json.loads(line)
  if row['tag']=='part':
   parts.append(row);assert row['consistent'],row
  elif row['tag']=='constant':
   c=row['constant'];db.execute('INSERT INTO decl VALUES(?,?,?,?,?,?,?)',(c['name'],row['side'],row['origin'],row['module'],row['path'],row['part'],json.dumps(c,separators=(',',':'))));count+=1;kinds[(row['side'],c['kind'])]+=1
   if c['unsafe'] or c['partial'] or c['kind']=='axiom':safety[(row['side'],c['kind'],c['unsafe'],c['partial'])]+=1
   if count%10000==0:db.commit()
  else:comparisons.append(row)
db.commit();db.execute('CREATE INDEX by_name ON decl(name)');db.commit()
audit=json.loads((E/'Port29SDKDATA_audit.json').read_text())
gp=next(p for p in audit['retained_outputs'] if p['path'].endswith('cross-origin-edges.jsonl'))
assert pin(gp['path'])==gp
graph=collections.defaultdict(set);og=collections.defaultdict(set);original=set();current=set();factor=set();cp=collections.defaultdict(set)
with Path(gp['path']).open() as f:
 for line in f:
  r=json.loads(line);n=r['name'];graph[n].update(r['dependencies'])
  if r['side']=='ORIGINAL':original.add(n);og[n].update(r['dependencies'])
  else:
   current.add(n);cp[n].add(str(CURRENT/'transport'/(r['module'].replace('.','/')+'.olean')))
   if r['module']=='S6SdkDependencyFactorV1':factor.add(n)
wp=next(p for p in audit['retained_outputs'] if p['path'].endswith('union-worklist.json'))
w=json.loads(Path(wp['path']).read_text());assert pin(wp['path'])==wp
root_seeds={l.split('\t')[1] for l in (OLD/'seeds.tsv').read_text().splitlines()}
aux='AspisR1.S2W_D189Wrappers.reserve._unsafe_rec';seeds=set(w['seeds'])-{aux}
def lookup(n):
 return [dict(name=n,side=s,origin=o,module=m,path=p,part=i,constant=json.loads(c)) for s,o,m,p,i,c in db.execute('SELECT side,origin,module,path,part,info FROM decl WHERE name=?',(n,))]
def closure(seeds,existing):
 seen=set();pending=list(seeds);gap=set();found={}
 while pending:
  n=pending.pop()
  if n in seen:continue
  seen.add(n)
  if n in existing:ds=existing[n]
  else:
   rows=lookup(n)
   if not rows:gap.add(n);continue
   found[n]=rows;ds={d for row in rows for d in row['constant']['dependencies']}
  pending.extend(ds-seen)
 return seen,gap,found
seen,gap,new=closure(seeds,graph)
oseen,ogap,onew=closure(root_seeds,og)
missing=json.loads((E/'Port29SDKDATA_missing-323.json').read_text())
provenance=[];extras={}
for r in missing:
 rows=lookup(r['name']);extras[r['name']]=rows
 provenance.append(dict(name=r['name'],current_available=r['name'] in current,
  complete_part_origins=[{k:v for k,v in x.items() if k!='constant'} for x in rows],
  status='ORIGINAL retained ConstantInfo available; equality pending below' if any(x['side']=='ORIGINAL' for x in rows) else
   'pinned CORE ConstantInfo available' if rows else 'CURRENTONLY candidate; original absent from all retained parts' if r['name'] in current else 'absent from original/core/CURRENT selected; Port18-only or unreleased data still needed',
  historical_assessment='Retained original object metadata observation; old unpinned parts not upgraded to a historical gate'))
for n in factor-original:extras[n]=lookup(n)
selected=collections.defaultdict(set);export_sources={}
for data in [new,onew,extras]:
 for n,rows in data.items():
  for row in rows:
   k=(row['side'],row['origin'],row['module'],row['path']);selected[k].add(n);export_sources[k]=row
extra_compare=collections.defaultdict(set)
for n,rows in extras.items():
 for row in rows:
  if row['side']=='ORIGINAL':
   for p in cp[n]:extra_compare[('full-original-current',row['path'],p)].add(n)
# The original full counterparts of all169 factor names are audited even when unselected.
for n in factor:
 for row in lookup(n):
  if row['side']=='ORIGINAL':
   for p in cp[n]:extra_compare[('full-original-current',row['path'],p)].add(n)
(out/'Port29SDKDATA_extra-compare.tsv').write_text(''.join('\t'.join([*k,*sorted(v)])+'\n' for k,v in sorted(extra_compare.items())))
with (out/'Port29SDKDATA_export.tsv').open('w') as f:
 for k,ns in sorted(selected.items()):
  side,origin,m,p=k;dest=str(out/'Port29SDKDATA_transports'/side/origin/m.replace('.','/'))
  f.write('\t'.join([side,origin,m,p,dest,*sorted(ns)])+'\n')
write(out/'Port29SDKDATA_new-provenance-323.json',provenance)
write(out/'Port29SDKDATA_new-closure.json',dict(union=dict(seeds=len(seeds),reachable=len(seen),raw_missing=sorted(gap),new_body_names=sorted(new),fixed_point=True),
 original=dict(seeds=len(root_seeds),reachable=len(oseen),raw_missing=sorted(ogap),new_body_names=sorted(onew),fixed_point=True),
 original_factor_counterparts={n:[{k:v for k,v in x.items() if k!='constant'} for x in lookup(n) if x['side']=='ORIGINAL'] for n in sorted(factor-original)},
 semantics='Name/edge fixed point only. Every origin retained; no strict conflict selection or kernel acceptance. Current-only bodies do not establish original equality.'))
write(out/'Port29SDKDATA_index-summary.json',dict(part_headers=len(parts),constant_observations=count,
 part_counts=dict(collections.Counter((r['side']+':'+str(r['part'])) for r in parts)),
 kinds={str(k):v for k,v in kinds.items()},safety={str(k):v for k,v in safety.items()},
 root_duplicate_observations=sum(r['tag']=='root-duplicate' for r in comparisons),
 cross_observations=sum(r['tag']=='original-current' for r in comparisons),
 raw_missing323_original_available=sum(any(x['side']=='ORIGINAL' for x in lookup(r['name'])) for r in missing),
 raw_missing323_core_available=sum(any(x['side']=='CORE' for x in lookup(r['name'])) for r in missing),
 extra_comparison_batches=len(extra_compare),extra_comparison_observations=sum(map(len,extra_compare.values())),
 export_modules=len(selected),export_name_origin_requests=sum(map(len,selected.values())),
 wall_seconds=time.monotonic()-start,peak_rss_bytes=resource.getrusage(0).ru_maxrss,swaps=resource.getrusage(0).ru_nswap,
 print_axioms='N/A: noncompiler index/closure; no declaration selection',
 source=pin(__file__)))
assert resource.getrusage(0).ru_maxrss<512*1024**2
# Publish only complete request artifacts; the Lean process has not freed any data into this process.
(out/'Port29SDKDATA_export-ready').write_text('ready\n')
db.close()
print(json.dumps(dict(index=count,union_missing=len(gap),original_missing=len(ogap),exports=len(selected),wall=time.monotonic()-start)))
