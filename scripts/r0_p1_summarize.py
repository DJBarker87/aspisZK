#!/usr/bin/env python3
"""Collect completed P1 measurements; never executes a verifier."""
from pathlib import Path
import json
out=Path(__file__).resolve().parent.parent/'results/r0-cost-probe-20261009'
groups=['Semantic','ChordClaims','Merkle','V1','V2','Other'];rows=[]
for configuration in ['c0','c1','c2','c3','c4','c5a','c5b','c5c']:
 measured='c3' if configuration=='c4' and (out/'c4-reuse.json').exists() else configuration
 for variant in ['transfer','withdrawal']:
  run=out/f'{measured}-diagnostic/{variant}-diagnostic-1.json'
  count=out/f'{measured}-{variant}-ops.json'
  if not run.exists() or not count.exists(): continue
  d=json.loads(run.read_text());o=json.loads(count.read_text());assert d['verifier_completed'] and d['execution']['error'] is None
  assert d['sbf_heap_high_water_bytes']<=256*1024
  assert not json.loads((out/f'{measured}-stack/stack-audit.json').read_text())['reachable_diagnostics']
  cu=dict.fromkeys(groups,0);ops={g:{} for g in groups}
  for p in d['phase_markers']:
   phase=p['phase'];g={'semantic':'Semantic','chord-claims':'ChordClaims','v2':'V2'}.get(phase,'Merkle' if phase.startswith('merkle:') else 'V1' if phase.startswith('v1:') else 'Other')
   if g!='Other': cu[g]+=p['delta_from_previous_cu']
  cu['Other']=d['execution']['cu']-sum(cu.values())
  for p in o['phases']:
   phase=p['phase'];g=phase if phase in groups else 'Merkle' if phase.startswith('Merkle(') else 'V1' if phase.startswith('V1(') else 'Other'
   for k,n in p['inclusive'].items():ops[g][k]=ops[g].get(k,0)+n
  counts={g:[sum(ops[g].get(x,0) for x in ks) for ks in [('EMul','EMulK','EMulF','ESquare'),('KMul','KMulF','KMulC','KSquare'),('FMul',)]] for g in groups}
  rows.append(dict(configuration=configuration.upper()+(' (C3 evidence)' if measured!=configuration else ''),fixture=variant,cu=cu,multiplications_inclusive=counts,total=d['execution']['cu'],proof_bytes=d['proof_bytes'],heap=d['sbf_heap_high_water_bytes'],headroom_to_1300000=1300000-d['execution']['cu']))
(out/'summary.json').write_text(json.dumps(rows,indent=2)+'\n')
table='| Configuration / fixture | Semantic CU [E/K/F] | ChordClaims CU [E/K/F] | Merkle CU [E/K/F] | V1 / batched query CU [E/K/F] | V2 / rounds CU [E/K/F] | Other CU [E/K/F] | Total CU | Proof bytes | Headroom to 1.3M |\n|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|\n'
for r in rows:
 cells=[r['configuration']+' / '+r['fixture']]+[f"{r['cu'][g]:,} [{'/'.join(format(n,',') for n in r['multiplications_inclusive'][g])}]" for g in groups]+[f"{r['total']:,}",f"{r['proof_bytes']:,}",f"{r['headroom_to_1300000']:,}"]
 table+='| '+' | '.join(cells)+' |\n'
old=(out/'phase-table.md').read_text();p=out/'REPORT-P1.md';p.write_text(p.read_text().replace(old,table));(out/'phase-table.md').write_text(table)
resources=[]
for p in sorted(out.glob('*.json')):
 d=json.loads(p.read_text())
 if isinstance(d,dict) and d.get('schema')=='aspis.v8-state-only-cu.resources.v1':resources.append(dict(evidence=p.name,**d))
(out/'resources.json').write_text(json.dumps(resources,indent=2)+'\n')
print(table)
