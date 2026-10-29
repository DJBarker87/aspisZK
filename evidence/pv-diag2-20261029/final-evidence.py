"""Collect exact provenance blocker and per-scope resource receipts; read-only."""
from pathlib import Path
import hashlib,json,re
D=Path('/home/dombarker/project-offloads/codex-pv-diag2-20261029');B=D.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
g=json.loads((D/'project-graph.json').read_text());r=json.loads((D/'project-resolution.json').read_text());cache=json.loads((D/'cache-preflight.json').read_text());rows=[]
for m,variants in r['gaps'].items():
 q=B/'codex-pv-rjdec-20261028/objects'/(m.replace('.','/')+'.olean');gp=Path(g[m]['path']) if m in g else None
 source=B/'codex-pv-runjoin-20261026/runjoin32-lean/sources'/(m.replace('.','/')+'.lean')
 row=dict(module=m,graph_entry=g.get(m),chosen_object=str(q),chosen_sha256=sha(q) if q.is_file() else None,graph_sha256=sha(gp) if gp and gp.is_file() else None,source_sha256=sha(source) if source.is_file() else None,tracked_variants=variants)
 row['same_object']=row['chosen_sha256']==row['graph_sha256'];rows.append(row)
(D/'cohort-blocker.json').write_text(json.dumps(dict(ruling='h7: no substituted source/object credit; stop affected binding/audit; exact pinned regeneration plus unchanged-importer elaboration needed if generation hash-chain authority cannot be recovered',gaps=rows,cache_mismatches=cache['mismatches'],source_bridge_release_credit=False),indent=2)+'\n')
scopes=[]
for p in sorted(D.glob('*-receipt.json')):
 x=json.loads(p.read_text());label=p.name[:-13];tim=D/(label+'-time.log');text=tim.read_text() if tim.exists() else ''
 metric=lambda pattern:re.search(pattern,text)
 rss=metric(r'Maximum resident set size \(kbytes\): (\d+)');swap=metric(r'Swaps: (\d+)');wall=metric(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([0-9:.]+)')
 x.update(label=label,peak_rss_kib=int(rss[1]) if rss else None,swaps=int(swap[1]) if swap else None,gnu_wall=wall[1] if wall else None,receipt_sha256=sha(p),output_sha256=sha(D/(label+'-output.log')),interval_from_mtime=dict(start=p.stat().st_mtime-x['wall_seconds'],end=p.stat().st_mtime,qualification='reconstructed from receipt mtime and recorded launch wall; not a compiler timestamp'))
 scopes.append(x)
ordered=sorted(scopes,key=lambda x:x['interval_from_mtime']['start']);overlaps=[]
for a,b in zip(ordered,ordered[1:]):
 if a['interval_from_mtime']['end']>b['interval_from_mtime']['start']:overlaps.append([a['label'],b['label']])
(D/'attempts.json').write_text(json.dumps(dict(scopes=scopes,native_scopes=sum(x['label'].startswith('native') for x in scopes),lean_attempts=sum(x['label'].startswith('lean') for x in scopes),reconstructed_scope_overlaps=overlaps,source_target_revision='9dab53f366',print_axioms_qualification='raw print output retained; failed/superseded runs and cohort-gated model compiles do not establish a deployed theorem'),indent=2)+'\n')
print('historical graph gaps',[(x['module'],x['same_object']) for x in rows]);print('recorded scopes',len(scopes),'reconstructed overlaps',overlaps)
