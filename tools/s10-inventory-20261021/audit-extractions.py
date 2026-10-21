#!/usr/bin/env python3
"""Validate and summarize retained extraction/resource receipts, without reruns."""
import hashlib,json
from pathlib import Path
E=Path(__file__).resolve().parents[2]/'docs/research/100bit-spend-path-20261013/evidence/s10-inventory-20261021'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
source=json.loads((E/'source-hashes.json').read_text());pins={s['path']:s['sha256'] for s in source['files']};rows=[]
for d in sorted((E/'extraction-attempts').iterdir()):
 r=json.loads((d/'receipt.json').read_text());limits=r['limits']
 assert limits=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0','pids.max':'64'},d
 assert r['wall_seconds']>=0 and r['peak_rss_kib']>0 and r['swaps']==0,d
 assert r['cgroup_memory_peak_bytes']<=8*2**30,d
 assert r['print_axioms']=='N/A: no Lean compilation',d
 command=r['command'];summary=d.name=='summary-v3'
 if not summary:
  assert '--release' in command and '--locked' in command and '--offline' in command,d
  program='programs/aspis-pool' if d.name.startswith('pool') else 'programs/r1-cost-probe'
  source_inputs={p:pins[p] for p in [program+'/Cargo.toml',program+'/src/lib.rs','Cargo.lock']}
  if d.name.startswith('pool'):source_inputs[program+'/src/processor.rs']=pins[program+'/src/processor.rs']
 else:source_inputs={}
 graph=E/(d.name+'.json');g=json.loads(graph.read_text()) if graph.exists() else None
 rows.append(dict(attempt=d.name,command=command,exit_status=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_bytes=r['peak_rss_kib']*1024,swaps=r['swaps'],aggregate_cgroup_peak_bytes=r['cgroup_memory_peak_bytes'],limits=limits,frozen_source_revision=source['source_revision'],wrapper_source_revision=r['source_revision'],source_inputs_sha256=source_inputs,print_axioms=r['print_axioms'],receipt_sha256=sha(d/'receipt.json'),retained_file_hashes={p.name:sha(p) for p in sorted(d.iterdir()) if p.is_file()},emitted_graph_sha256=sha(graph) if g else None,charon_has_errors=g.get('has_errors') if g else None,review_stop=(d/'review-stop.json').exists(),classification='JSON summarization only' if summary else 'INCOMPLETE diagnostic; no full frozen graph certificate'))
result=dict(schema='s10-extraction-attempt-reconciliation-v1',source_revision=source['source_revision'],source_provenance_sha256=sha(E/'source-provenance.json'),source_manifest_sha256=sha(E/'source-hashes.json'),launcher_sources_sha256={p.name:sha(p) for p in sorted(Path(__file__).parent.glob('*host*.py'))},attempts=rows)
(E/'extraction-summary.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps(dict(attempts=len(rows),stopped=sum(r['review_stop'] for r in rows),status='INCOMPLETE')))
