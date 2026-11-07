#!/usr/bin/env python3
"""Make module/configuration evidence and unknown fields explicit in the plan."""
from pathlib import Path
import json
E=Path(__file__).resolve().parent;p=json.loads((E/'NMH_PLAN.json').read_text());inv={z['blob']:z for z in json.loads((E/'NMH_INVENTORY.json').read_text())['blobs']}
def vals(cmd,k):return [cmd[i+1] for i,s in enumerate(cmd[:-1]) if s==k]
for g in p['groups']:
 zs=[inv[h] for h in g['members']]
 g['source_modules']=sorted({a['source'] for z in zs for a in z['annotations']})
 g['annotated_symbols']=sorted({a['name'] for z in zs for a in z['annotations']})
 g['configuration_origin_statuses']=sorted({z['origin_status'] for z in zs})
 g['missing_configuration_fields']=[] if g['configuration_candidates'] else ['source_manifest/driver','feature selection','opaque list','entry function set']
 g['configuration_caveat']='Source annotations enumerate declarations, not an extractor entry set. Same-packet command metadata is a candidate until byte comparison; no historical hash link is invented.'
for r in p['runs']:
 c=r['charon_command'];r['execution_group']=r['run'].replace('E','RUN_G',1);r['source_manifest']=vals(c,'--manifest-path')[0];r['function_set']=vals(c,'--start-from');r['opaque_list']=vals(c,'--opaque');r['feature_set']=dict(default_features='--no-default-features' not in c,explicit=vals(c,'--features'));r['right_configuration_reason']=r['basis']
p['group_semantics']='groups partitions336 blobs by source/namespace and metadata. runs is authoritative execution grouping: exactly one Charon-then-Aeneas configuration per entry. Candidate membership is not a historical origin assertion.'
(E/'NMH_PLAN.json').write_text(json.dumps(p,indent=2)+'\n');print('plan now explicitly records source modules, annotated symbols, function/feature/opaque selections and missing fields')
