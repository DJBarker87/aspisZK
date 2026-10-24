"""Validate retained focused evidence against final source and live hash inventory."""
from pathlib import Path
import json,re,hashlib,subprocess
D=Path(__file__).resolve().parent;R=D.parents[2]
L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
E=R/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/rng-material'
sha=lambda b:hashlib.sha256(b).hexdigest()
for script,args in [('bind.py',['003']),('adapt.py',[]),('make-audit.py',[])]:
 subprocess.run(['python3',str(D/script),*args,'--check'],check=True)
rows=[json.loads(p.read_text()) for p in sorted(E.glob('*-receipt.json'))]
assert len(rows)==27 and [r['attempt'] for r in rows]==list(range(11524,11551))
latest={}
for r in rows:
 if r['exit_status']==0:latest[r['module']]=r
live={r['path']:r for r in json.loads((E/'current-closure-hashes.json').read_text())['files']}
modules=[]
for p in sorted(L.glob('ProverRwRngMaterial*.lean')):
 module='R1Z/'+p.stem;r=latest[module]
 assert sha(p.read_bytes())==r['source_sha256'],(module,'source mismatch')
 assert live[r['source_path']]['sha256']==r['source_sha256']
 for d in r['dependencies']:
  assert live[d['resolved_object']]['sha256']==d['object_sha256'],(module,d['module'],'dependency changed')
 obj='/home/dombarker/project-offloads/aspis-joint-20261019/objects/'+module+'.olean'
 modules.append(dict(module=module,attempt=r['attempt'],source_sha256=r['source_sha256'],object_sha256=live[obj]['sha256'],deps_fingerprint=r['deps_fingerprint']))
audit=latest['R1Z/ProverRwRngMaterialAudit'];assert audit['attempt']==11550 and len(audit['print_axioms'])==38
allowed={'propext','Classical.choice','Quot.sound'}
for line in audit['print_axioms']:
 if 'depends on axioms:' in line:
  axioms={x.strip() for x in line.split('[',1)[1].split(']',1)[0].split(',')}
  assert axioms<=allowed,line
 assert 'sorryAx' not in line
old=subprocess.check_output(['git','show','e9e2ffa9c4:docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngMaterialBodyEmission.lean'],cwd=R)
prefix=old.rsplit(b'end ProverRwRngMaterialBody',1)[0]
assert (L/'ProverRwRngMaterialBodyEmission.lean').read_bytes().startswith(prefix)
a=json.loads(subprocess.check_output(['git','show','e9e2ffa9c4:tools/prover-rw-20261023/rng-material/adaptation.json'],cwd=R))
b=json.loads((D/'adaptation.json').read_text())
assert a['type_parameters']==b['type_parameters'] and a['local_leaves']==b['local_leaves']
assert not subprocess.check_output(['git','diff','--name-only','dbc123fdc8','--','crates','programs'],cwd=R).strip()
source_map=json.loads((D/'source-map.json').read_text())
record=dict(schema='rng-material-final-focused-assessment-v1',proof_revision=audit['source_revision_full'],audit=dict(attempt=11550,target=audit['module'],command=audit['effective_lean_command'],exit_status=audit['exit_status'],time_log=audit['time_log'],full_axioms=audit['print_axioms']),modules=modules,source_map=dict(declarations=len(source_map['declarations']),files=len(source_map['source_files']),assessment=source_map['source_assessment']),previous_emitted_body_prefix_unchanged=True,external_parameter_signatures_unchanged=True,all_current_module_sources_match_green_receipts=True,all_recorded_dependency_objects_match_live_inventory=True,shipped_source_changed=False,validation_scope='Focused emitted source conditional control; cached pinned Aeneas imports reused. No full frozen manifest, native runtime identity or ELF gate.',failed_lean_attempts=[r['attempt'] for r in rows if r['exit_status']!=0],budget=json.loads((E/'ledger.json').read_text()),retained_boundaries=['16 TypeLeaves and 41 LocalLeaves/component interfaces uninstalled','cells and active-row components; first_inactive_row and four sampling components','filesystem reserve_fallible component; no durable filesystem correctness','getrandom NonZeroI32 sort/result/destruction transport; actual secure factory callback','physical zeroization/Drop and external borrowed-provider transport','successful full body/audit/event/bytes-context-to-Raw association; body_success remains conditional on body reply','full cap8 draw inventory and L1/L2; both deployed targets not yet established'],unchanged_probability_event='ProverCommitPublicNonce40.E1; no new freshness, independence or retry law')
(E/'summary.json').write_text(json.dumps(record,indent=2)+'\n')
print('Validated',len(modules),'current green modules, 38 standard-axiom reports; cumulative Lean',record['budget']['cumulative_used'])
