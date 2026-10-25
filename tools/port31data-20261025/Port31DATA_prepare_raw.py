#!/usr/bin/env python3
"""Bounded presentation-only fragment preselection; actual Names read by Lean."""
import collections,hashlib,json,subprocess,time,resource
from pathlib import Path
from Port31DATA_run import T,E,SYS,pin,state,safe
from Port31DATA_prepare import obj,write,base
start=time.monotonic();n=354
assert json.loads((E/'Port31DATA_attempt-353.json').read_text())['accepted']
r=base(n);out=Path(r['directory']);out.mkdir(mode=0o700,exist_ok=True)
fresh={x['path']:x for x in r['fresh_pins']};states={x['path']:x for x in r['states']}
def add(p,expected=None,rehash=False):
 p=safe(p);s=state(p);assert not str(p).startswith('/Users/dominic/ZK/.worktrees/') or p.is_relative_to(T.parents[1])
 if expected:assert s[2]==expected['bytes']
 if rehash:
  q=pin(p)
  if expected:assert q['sha256']==expected['sha256'],str(p)
  fresh[str(p)]=q
 states[str(p)]=dict(path=str(p),stat=s,byte_pin=(expected or {}).get('sha256'),assessment='fresh bytes' if rehash else 'published byte pin REUSED; fresh safe/stat continuity only, not a new identity gate')
 return str(p)
# Fresh two newly released objects; source pin assessment remains historical main only.
release=Path('/private/tmp/lead-s8-body-release-20261025-v1')
assert pin(release/'manifest.json')['sha256']=='17219a7477f604eaa0d94ba22276aa395083465e505d28b940536f0f5b8d27a5'
add(release/'manifest.json',rehash=True)
s8=json.loads((release/'manifest.json').read_text());historical=obj('evidence/port17release-20261024/root-local-pins-final.json','904745b496')
inputs=[];newbody=[]
for row in s8['rows']:
 if row.get('absent'):continue
 h=next(x for x in historical if x['name']==row['module'])
 assert h['sha256']==row['sha256'] and h['bytes']==row['bytes']
 p=Path(row['retained_path']);add(p,row,True)
 for suffix in ['.server','.private']:assert not Path(str(p)+suffix).exists() and not Path(str(p)+suffix).is_symlink()
 inputs.append(('S8:'+row['module'],str(p)));newbody.append(dict(module=row['module'],path=str(p),pin=row['sha256'],suffixes='absent, observed; not invented'))
# Reuse the reviewed old graph to choose only fragment containers. Never logical selection.
au=obj('evidence/port29sdkdata-20261025/Port29SDKDATA_Strict-v3-final-audit.json')
gp=next(x for x in au['artifacts'] if x['path'].endswith('cross-origin-edges-final.jsonl'))
add(gp['path'],gp)
graph=collections.defaultdict(set)
with Path(gp['path']).open() as f:
 for line in f:
  q=json.loads(line);graph[q['name']].update(q['dependencies'])
roots=['AspisR1.S2W_D189Consolidation.accepted_run','AspisS1SdkSelectedSemanticTrace.original_sdk_selected_semantic_trace','AspisS6SdkSelectedSemanticCaller.original_sdk_selected_cuts']
releases=[('BASE','s126-sdk-current-9acc-proof-refresh-20261024-v1','e55b656c8c5abb11c769f4a5c6b5e5ab574e061b437a26240c2c65c25c542226','constants.jsonl'),('INCREMENTAL','s126-sdk-current-incremental-release-20261024-v1','49c56b6cfa3ace9d747c9616bfbaea48c39823089adb2eb0bfaacc7cec1e0e83','constants-incremental.jsonl'),('SELECTED','s126-sdk-selected-cut-release-20261025-v1','3af7fd6e890416e849dc952a5ad13466dddf88148acced8c3ea23e9bc8c5224f','constants-incremental.jsonl')]
# Selected delta edges are included for initial module reach, without converting names.
q=Path('/private/tmp/s126-sdk-selected-cut-release-20261025-v1/edges-incremental.jsonl');add(q,rehash=True)
with q.open() as f:
 for line in f:
  x=json.loads(line)
  if isinstance(x,list):m,name,ds=x
  else:name,ds=x['name'],x['dependencies']
  graph[name].update(ds)
reach=set();todo=list(roots)
while todo:
 name=todo.pop()
 if name in reach:continue
 reach.add(name);todo.extend(set(graph.get(name,()))-reach)
# Keep all reviewed conflicts even if a future selected graph prunes them.
gaps=obj('evidence/port29sdkdata-20261025/Port29SDKDATA_Strict-v3-final-gaps.json')
forced=set(gaps['conflicting13'])
want=reach|forced
meta=[]
for label,dirname,sha,constantfile in releases:
 root=Path('/private/tmp')/dirname;mp=root/'manifest.json';assert pin(mp)['sha256']==sha
 add(mp,rehash=True);m=json.loads(mp.read_text());cp=root/constantfile
 add(cp,next((x for x in m['files'] if x['relative']==constantfile),None))
 modules=set()
 with cp.open() as f:
  for line in f:
   x=json.loads(line)
   if x['name'] in want:modules.add(x['module'])
 count=0
 for file in m['files']:
  rel=file['relative']
  if not rel.startswith('transport/'):continue
  mod=rel[10:-6].replace('/','.')
  if mod not in modules:continue
  p=add(root/rel,file);inputs.append(('CURRENT:'+label+':'+mod,p));count+=1
 meta.append(dict(label=label,available_fragments=sum(f['relative'].startswith('transport/') for f in m['files']),selected_fragments=count,manifest=pin(mp)))
# Original/core reviewed194+256 raw-body readbacks; preserve all origins/parts.
a=obj('evidence/port29sdkdata-20261025/Port29SDKDATA_final-audit.json')
oldm=a['external_transport_manifest'];add(oldm['path'],oldm,True)
newm=next(x for x in au['artifacts'] if x['path'].endswith('transports-final.json'));add(newm['path'],newm,True)
oldrows=json.loads(Path(oldm['path']).read_text())['transports'];newrows=json.loads(Path(newm['path']).read_text())['transports']
assert len(oldrows)==194 and len(newrows)==256
ocount=0
for group,rows in [('PRIOR194',oldrows),('PRIOR256',newrows)]:
 for i,row in enumerate(rows):
  if not want.intersection(row['names']):continue
  p=add(row['path'],row);inputs.append((group+':'+str(i)+':'+row['side']+':'+row['module'],p));ocount+=1
# Ordinary checked fresh theorem is read as data, never used as a trusted project import.
bp=next(x for x in json.loads((E/'Port31DATA_attempt-353.json').read_text())['outputs'] if x['path'].endswith('.olean'))
add(bp['path'],bp,True);inputs.append(('BOOL:NEW-PROOF',bp['path']))
for name in ['Port31DATA_make_reader.py','Port31DATA_reader-body.lean.txt','Port31DATA_prepare_raw.py']:
 add(T/name,rehash=True)
for name in ['Lean.olean','Lean.olean.server','Lean.olean.private']:
 p=SYS/'lib/lean'/name
 if p.exists():add(p,rehash=True)
add(SYS/'src/lean/Lean/Util/FoldConsts.lean',rehash=True)
rawbytes=sum(Path(p).stat().st_size for _,p in inputs);assert rawbytes<=512*1024**2,rawbytes
assert len({p for _,p in inputs})==len(inputs)
wl=out/'Port31DATA_inputs.tsv';wl.write_text(''.join(label+'\t'+path+'\n' for label,path in inputs));add(wl,rehash=True)
r.update(fresh_pins=list(fresh.values()),states=list(states.values()),raw_inputs=len(inputs),raw_bytes=rawbytes,release=newbody,fragments=meta,original_core_fragments=ocount,presentation_preselection=dict(reached=len(reach),missing=len(reach-graph.keys()),forced_conflicts=sorted(forced),logical_selection=False),reuse='194+256 strict readbacks and1432 additive current fragments; only selected containers stat-checked, no8917 scan or2.8GB rehash',core_dependency_assessment='Pinned installed Lean4.32 core; historical full-core inventory reused, selected Init/Lean objects and tool runtime freshly hashed. No fresh full-core tree identity gate.',command=['python3','-B',str(Path(__file__))],exit_status=0,wall_seconds=time.monotonic()-start,peak_rss_bytes=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,swaps=resource.getrusage(resource.RUSAGE_SELF).ru_nswap)
write(E/'Port31DATA_preflight-354.json',r)
print(json.dumps({k:r[k] for k in ['raw_inputs','raw_bytes','original_core_fragments','fragments','presentation_preselection','wall_seconds','peak_rss_bytes']}))
