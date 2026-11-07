#!/usr/bin/env python3
"""Use known corpus namespaces for unlaunched matching-source diagnostic probes.
Namespace is observed metadata, not a normalization or an origin assertion.
"""
from pathlib import Path
import json
E=Path(__file__).resolve().parent;p=json.loads((E/'NMH_PLAN.json').read_text());inv={z['blob']:z for z in json.loads((E/'NMH_INVENTORY.json').read_text())['blobs']};changes=[]
for r in p['runs']:
 if not r.get('diagnostic_only') or int(r['run'][5:])<20:continue
 assert not (E/r['run']/'receipt.json').exists() and not (E/(r['run']+'-admission.json')).exists()
 source='aspis_core' if 'aspis-core/Cargo.toml' in r['configuration']['manifest'] else 'aspis_r1_cost_probe'
 candidates=sorted((inv[h] for h in r['members'] if inv[h]['crate_header']==[source] and len(inv[h]['namespace'])==1),key=lambda z:z['bytes'])
 if not candidates:continue
 ns=candidates[0]['namespace'][0];ac=r['aeneas_command'];ac[ac.index('-namespace')+1]=ns;ac[ac.index('-subdir')+1]=ns
 r['configuration']['namespace']=[ns];r['configuration']['aeneas_command']=ac;r['basis']+=' Output namespace taken exactly from matching-source corpus member '+candidates[0]['blob']+'; not normalized away. Entry/feature configuration remains diagnostic.'
 (E/(r['run']+'_spec.json')).write_text(json.dumps(r,indent=2)+'\n');changes.append(dict(run=r['run'],namespace=ns,blob=candidates[0]['blob']))
p['diagnostic_namespace_inputs']=changes;(E/'NMH_PLAN.json').write_text(json.dumps(p,indent=2)+'\n');print(json.dumps(changes))
