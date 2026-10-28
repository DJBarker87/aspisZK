"""Lane-owned additive ledger overlay; calls the unchanged NCZ invariant validator.
The NCZ full recomputation CLI accepts its frozen merged index only, so this
records structural validation separately from adoption into that index.
"""
from pathlib import Path
import json,hashlib,importlib.util,collections
E=Path(__file__).resolve().parent;R=E.parent.parent
base=R/'evidence/native-compledger-20261028/NCZ_LEDGER.json'
d=json.loads(base.read_text());inv=json.loads((E/'NDH_INVENTORY.json').read_text())
rows=[
('crates/aspis-core/src/r0/domain.rs::FibreIndex::get',11,12,'NDH_Geometry.get','Every valid FibreIndex (0<=value<262144), constructed from that same usize; identity reference/carrier.'),
('crates/aspis-r1-cost-probe/src/compact.rs::slot_offset',45,46,'NDH_Slots.reference + NDH_SlotInduction.invariant/completion','slot<=6; at=slotStart(i) and i<slot<=6 at each loop step; exact source update and complete natural induction.'),
('crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV1::is_immutable',33,34,'NDH_RegistrySlots.immutable_v1','All native V1 record fields, arbitrary flags; free AdapterRw op25 instance on the same flags field.'),
('crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV1::is_paused',35,36,'NDH_RegistrySlots.paused_v1','All native V1 record fields, arbitrary flags; free AdapterRw op26 instance on the same flags field.'),
('crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV2::is_immutable',37,38,'NDH_RegistrySlots.immutable_v2','All native V2 record fields, arbitrary flags; free AdapterRw op27 instance on the same flags field.'),
('crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV2::is_paused',39,40,'NDH_RegistrySlots.paused_v2','All native V2 record fields, arbitrary flags; free AdapterRw op28 instance on the same flags field.')]
closures=[]
for f,pos,neg,theorem,domain in rows:
 suffix=f.split('::',1)[1]
 ids=[f'NDH_K{n:03}' for n in [pos,neg]]
 receipts=[json.loads((E/a/'receipt.json').read_text()) for a in ids]
 assert receipts[0]['exit_status']==0 and receipts[1]['exit_status']!=0
 assert 'VERIFICATION:- SUCCESSFUL' in (E/ids[0]/'stdout.log').read_text()
 assert 'Failed to match' not in (E/ids[1]/'stdout.log').read_text()
 assert 'timed out' not in (E/ids[1]/'stdout.log').read_text()
 cid='NDH::'+suffix;hyp=[dict(name='NDH.PacketDomain',statement=domain,discharged_by=None),dict(name='NDH.PhysicalInterpretation',statement='Same native/cohort input carrier, reference extraction and owner-approved P6/D188 contract semantic transport; caller/installed-dictionary association remains explicit.',discharged_by=None)]
 paths=[str((E/a/'receipt.json').relative_to(R)) for a in ids]
 paths+=[str((E/a/'stdout.log').relative_to(R)) for a in ids]
 paths+=[str((E/(a+'-graph-check.json')).relative_to(R)) for a in ids]
 paths += ['evidence/native-front5-20261028/NDH_FRONTIER_BRIDGES.md']
 for p in paths:
  b=(R/p).read_bytes();d['evidence_manifest'][p]={'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
 claim=dict(claim_id=cid,function=f,admissible_local_credit=True,quarantined_support=[],feature_parity='deployed verifier default/private-leaf-salts/optimized-terminal/program-build; resolved lists in every graph receipt',named_hypotheses=hyp,evidence=paths,receipts=paths[:2],medium='Kani contract + NCO-pinned reference extraction + Lean equation',source_claim_text=domain,reported_status='CLOSED-CONDITIONAL',limitations='Local domain only. No caller, whole SDK, ELF rebuild, or headline soundness closure.',composition_trust='P6/D188 native contract semantic transport reclassification, not removal')
 d['claims'].append(claim)
 for r in d['rows']:
  if r['function']!=f:continue
  r.update(bridge_status='CLOSED-CONDITIONAL',selected_claims=[cid],named_hypotheses=hyp,feature_parity_summary=claim['feature_parity'],no_credit_reason=None)
  r['claim_ids'].append(cid);r['evidence']+=paths;r['receipts']+=paths[:2]
  for p in paths[:2]:r['receipt_sha256'][p]=d['evidence_manifest'][p]['sha256']
 closures.append(dict(function=f,status='CLOSED-CONDITIONAL',domain=domain,theorem=theorem,kani=ids,composed_status='OPEN'))
for tx in ['TX1','TX2','all_rows']:
 chosen=[r for r in d['rows'] if tx=='all_rows' or r['transaction']==tx]
 d['coverage'][tx]['local_bridge_status']=dict(collections.Counter(r['bridge_status'] for r in chosen))
status_by_function={r['function']:r['bridge_status'] for r in d['rows']}
d['coverage']['unique_functions']['local_bridge_status']=dict(collections.Counter(status_by_function.values()))
for r in d['rows']:
 for o in r['caller_domain_obligations']:
  if o.get('callee') in status_by_function:o['callee_local_status']=status_by_function[o['callee']]
d['NDH_overlay']={'baseline_sha256':hashlib.sha256(base.read_bytes()).hexdigest(),'scope':'local conditional evidence only; baseline critical_path graph retained as historical ranking, not recomputed or adopted','closures':closures}
(E/'NDH_LEDGER.json').write_text(json.dumps(d,indent=2)+'\n')
(E/'NDH_LEDGER_DELTA.json').write_text(json.dumps(dict(schema_version=1,baseline=str(base.relative_to(R)),closures=closures,open=[r['representative'] for r in inv if r['representative'] not in {c['function'] for c in closures}],composed_status='OPEN'),indent=2)+'\n')
spec=importlib.util.spec_from_file_location('NCZ_validate',R/'evidence/native-compledger-20261028/NCZ_validate.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);m.validate_invariants(d)
(E/'NDH_LEDGER_VALIDATION.json').write_text(json.dumps(dict(exit_status=0,validator='unchanged NCZ_validate.py::validate_invariants',validator_sha256=hashlib.sha256((R/'evidence/native-compledger-20261028/NCZ_validate.py').read_bytes()).hexdigest(),ledger_sha256=hashlib.sha256((E/'NDH_LEDGER.json').read_bytes()).hexdigest(),local_conditional=len(closures),composed_closed=0,full_index_recomputation=False),indent=2)+'\n')
print('NCZ invariants PASS;',len(closures),'local conditional domains; 0 composed closures')
