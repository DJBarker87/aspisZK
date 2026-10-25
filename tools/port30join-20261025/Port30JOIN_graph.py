"""One new three-root presentation graph projection; no raw-body/kernel audit.
Published immutable graph evidence only. No byte rehash of historical payloads.
"""
import collections,json,pathlib,stat,hashlib,time,resource,subprocess
E=pathlib.Path('evidence/port30join-20261025')
p=pathlib.Path('/private/tmp/Port29SDKDATA-Strict-v3-fbc97427f15f4bdcb73d727c4e8c1680/Port29SDKDATA_Strict-v3-cross-origin-edges-final.jsonl')
q=pathlib.Path('/private/tmp/s126-sdk-selected-cut-release-20261025-v1/edges-incremental.jsonl')
roots=['AspisR1.S2W_D189Consolidation.accepted_run',
'AspisS1SdkSelectedSemanticTrace.original_sdk_selected_semantic_trace',
'AspisS6SdkSelectedSemanticCaller.original_sdk_selected_cuts']
t=time.monotonic();g=collections.defaultdict(set);origins=collections.defaultdict(set);pins=[]
for f in [p,q]:
 s=f.lstat();assert stat.S_ISREG(s.st_mode)
 pins.append(dict(path=str(f),size=s.st_size,mtime_ns=s.st_mtime_ns,device=s.st_dev,inode=s.st_ino,
                  validation='stat continuity only; prior byte hash reused, not revalidated'))
 with f.open() as h:
  for line in h:
   x=json.loads(line)
   if isinstance(x,list):
    assert len(x)==3; x=dict(module=x[0],name=x[1],dependencies=x[2])
   n=x['name'];g[n].update(x['dependencies']);origins[n].add(x.get('module','unknown'))
 # Input is immutable published data; guard stat continuity during this read.
 s2=f.lstat();assert (s.st_size,s.st_mtime_ns,s.st_ino)==(s2.st_size,s2.st_mtime_ns,s2.st_ino)
seen={};todo=collections.deque((r,None) for r in roots)
while todo:
 n,parent=todo.popleft()
 if n in seen:continue
 seen[n]=parent
 todo.extend((d,n) for d in sorted(g.get(n,())) if d not in seen)
missing=sorted(set(seen)-g.keys())
old=json.loads(subprocess.check_output(['git','show','74a62fd7b6:evidence/port29sdkdata-20261025/Port29SDKDATA_Strict-v3-final-gaps.json']))
oldmissing={x['name']:x for x in old['remaining']}
def path(n):
 out=[n]
 while seen[n] is not None:n=seen[n];out.append(n)
 return list(reversed(out))
report=dict(status='PRESENTATION APPROXIMATION ONLY; not exact Name or selected kernel closure',
 roots=roots,reachable=len(seen),known=len(set(seen)&g.keys()),missing=missing,
 needed_gap_records=[dict(oldmissing[n],witness_path=path(n)) if n in oldmissing else dict(name=n,witness_path=path(n)) for n in missing],
 union_gap_names_not_reached=sorted(set(oldmissing)-set(seen)),
 conflict_candidates_reached=[dict(name=n,witness_path=path(n)) for n in old['conflicting13'] if n in seen],
 source_selected12_added=True,exact_name_reader_required=True,whole_factor_literal_identity=False,
 inputs=pins,prior_graph_sha256='5f402847c32a1f7c4811e1015a158fbc81e6cc04a16fa05db1ad33229fdee749',
 incremental_edges_sha256='fa71d978aafc04b1a2f7248c5e913a39bc1cdd8639a0844d6820dbbf808357a4',
 command=['python3','tools/port30join-20261025/Port30JOIN_graph.py'],exit=0,wall_seconds=time.monotonic()-t,
 peak_rss_bytes=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,swap='not sampled; no compiler',axioms='N/A',
 source_revision=subprocess.check_output(['git','rev-parse','HEAD']).decode().strip())
(E/'focused-graph.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:report[k] for k in ['reachable','known','missing','union_gap_names_not_reached','wall_seconds','peak_rss_bytes']}))
