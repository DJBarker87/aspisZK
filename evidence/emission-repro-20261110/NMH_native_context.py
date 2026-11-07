#!/usr/bin/env python3
"""Put diagnostic core-only probes in the source crate named by their annotations."""
from pathlib import Path
import json
E=Path(__file__).resolve().parent;p=json.loads((E/'NMH_PLAN.json').read_text());changed=[]
for r in p['runs']:
 roots=r['configuration']['roots']
 if not r.get('diagnostic_only') or not all(n.startswith('aspis_core::') for n in roots):continue
 assert not (E/r['run']/'receipt.json').exists(),'do not mutate an attempted configuration'
 cc=r['charon_command'];cc=[s.replace('aspis_core::','crate::') for s in cc];cc[cc.index('--manifest-path')+1]=cc[cc.index('--manifest-path')+1].replace('crates/aspis-r1-cost-probe/','crates/aspis-core/');cc[cc.index('--features')+1]='r0'
 r['charon_command']=cc;r['configuration']['charon_command']=cc;r['configuration']['roots']=[n.replace('aspis_core::','crate::') for n in roots];r['configuration']['manifest']='crates/aspis-core/Cargo.toml';r['configuration']['features']=['r0'];r['basis']+=' Core-only probe uses core root rather than verifier dependency, matching corpus field.* declaration names; r0 is the deployed core feature. Original historical full configuration is still not recovered.'
 (E/(r['run']+'_spec.json')).write_text(json.dumps(r,indent=2)+'\n');changed.append(r['run'])
p['core_diagnostic_context']=changed;(E/'NMH_PLAN.json').write_text(json.dumps(p,indent=2)+'\n');print('source-crate diagnostic contexts:',','.join(changed))
