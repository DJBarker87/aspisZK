#!/usr/bin/env python3
"""Focused noncompiler fixed point; preserve all origins, no environment/selection."""
import collections,json,resource,sqlite3,subprocess,sys,time
from pathlib import Path
from Port29SDKDATA_diagnostic import E,OLD,pin,write
from Port29SDKDATA_strict3 import NEW,PREP,obj
start=time.monotonic();out=Path(sys.argv[1]);prep=json.loads(PREP.read_text())
while not (out/'Port29SDKDATA_index-ready').exists():time.sleep(.1)
audit=json.loads((E/'Port29SDKDATA_final-audit.json').read_text())
gp=next(x for x in audit['external_outputs'] if x['path'].endswith('final-cross-origin-edges.jsonl'))
graph=collections.defaultdict(set);original=collections.defaultdict(set);known=set();oknown=set()
with Path(gp['path']).open() as f:
 for line in f:
  r=json.loads(line);n=r['name'];known.add(n);graph[n].update(r['dependencies'])
  if r['side'] in ['ORIGINAL','CORE']:oknown.add(n);original[n].update(r['dependencies'])
db=sqlite3.connect(out/'Port29SDKDATA_focused.sqlite');db.execute('PRAGMA cache_size=-16000');db.execute('PRAGMA mmap_size=0');db.execute('CREATE TABLE decl(name,side,origin,module,path,part,info)')
newedges=[]
with (out/'Port29SDKDATA_raw.jsonl').open() as f:
 for line in f:
  r=json.loads(line)
  if r['tag']=='part':assert r['consistent']
  if r['tag']!='constant':continue
  c=r['constant'];db.execute('INSERT INTO decl VALUES(?,?,?,?,?,?,?)',(c['name'],r['side'],r['origin'],r['module'],r['path'],r['part'],json.dumps(c,separators=(',',':'))))
  if r['side']=='CURRENT-INCREMENTAL':
   n=c['name'];known.add(n);graph[n].update(c['dependencies']);newedges.append(dict(side=r['side'],origin=r['origin'],module=r['module'],path=r['path'],part=r['part'],**c))
db.execute('CREATE INDEX by_name ON decl(name)');db.commit()
old=sqlite3.connect('file:'+prep['prior_sqlite']['path']+'?mode=ro',uri=True);old.execute('PRAGMA cache_size=-16000');old.execute('PRAGMA mmap_size=0')
allowed={r['path'] for r in prep['states']}
can=obj('evidence/port18coherence-20261024/canonical-manifest.json');origins={r['name']:r['origin'] for r in can['declarations']}
def lookup(n,original_only=False):
 rows=[]
 for conn in [db,old]:
  for side,origin,m,p,part,info in conn.execute('SELECT side,origin,module,path,part,info FROM decl WHERE name=?',(n,)):
   if original_only and not (side in ['ORIGINAL','CORE'] or side=='PORT18-RAW' and origin=='root' or side=='PORT18-CHECKED' and origins.get(n,'').startswith('root:')):continue
   if p not in allowed:continue
   rows.append(dict(side=side,origin=origin,module=m,path=p,part=part,constant=json.loads(info)))
 return rows
selected=collections.defaultdict(set)
def closure(seeds,g,k):
 seen=set();todo=list(seeds);gaps=set()
 while todo:
  n=todo.pop()
  if n in seen:continue
  seen.add(n)
  if n in k:ds=g[n]
  else:
   rows=lookup(n,g is original)
   if not rows:gaps.add(n);continue
   ds=set()
   for r in rows:
    selected[(r['side'],r['origin'],r['module'],r['path'])].add(n)
    ds.update(r['constant']['dependencies'])
  todo.extend(ds-seen)
 return seen,gaps
wa=json.loads((E/'Port29SDKDATA_audit.json').read_text());wp=next(p for p in wa['retained_outputs'] if p['path'].endswith('union-worklist.json'));w=json.loads(Path(wp['path']).read_text())
aux='AspisR1.S2W_D189Wrappers.reserve._unsafe_rec';oldseeds=set(w['seeds'])-{aux}
newseeds=set(json.loads((NEW/'input.json').read_text())['seeds'])-{aux}
reach,gaps=closure(oldseeds|newseeds,graph,known)
oldreach,oldgaps=closure(oldseeds,graph,known)
rootseeds={l.split('\t')[1] for l in (OLD/'seeds.tsv').read_text().splitlines()}
oreach,ogaps=closure(rootseeds,original,oknown)
# Include actual bodies for the prior54 even when a graph change leaves them unreachable.
missing=json.loads((E/'Port29SDKDATA_final-gaps.json').read_text())['combined_raw_gaps'];provenance=[]
for row in missing:
 n=row['name'];rs=lookup(n)
 for r in rs:selected[(r['side'],r['origin'],r['module'],r['path'])].add(n)
 provenance.append(dict(name=n,prior_origin=row['port18_manifest_origin'],new_origins=[{k:v for k,v in r.items() if k!='constant'} for r in rs],available_in_current_incremental=n in {e['name'] for e in newedges},body_found=bool(rs) or n in known))
with (out/'Port29SDKDATA_export.tsv').open('w') as f:
 for i,(k,names) in enumerate(sorted(selected.items())):
  dest=str(out/'Port29SDKDATA_transports'/str(i));f.write('\t'.join([*k,dest,*sorted(names)])+'\n')
(out/'Port29SDKDATA_extra-compare.tsv').write_text('')
write(out/'Port29SDKDATA_stage3-closure.json',dict(seeds=len(oldseeds|newseeds),reachable=len(reach),gaps=sorted(gaps),old_seeds_reachable=len(oldreach),old_seeds_gaps=sorted(oldgaps),original_only_reachable=len(oreach),original_only_gaps=sorted(ogaps),prior54=provenance,export_sources=len(selected),export_names=sum(map(len,selected.values())),new_current_observations=len(newedges),semantics='Conservative dependency union, all variants retained; no coherent selection, original equality or kernel claim',wall_seconds=time.monotonic()-start,peak_rss_bytes=resource.getrusage(0).ru_maxrss,swaps=resource.getrusage(0).ru_nswap))
with (out/'Port29SDKDATA_incremental-edges.jsonl').open('x') as f:
 for r in newedges:f.write(json.dumps(r,separators=(',',':'))+'\n')
(out/'Port29SDKDATA_export-ready.tmp').write_text('ready\n');(out/'Port29SDKDATA_export-ready.tmp').replace(out/'Port29SDKDATA_export-ready')
