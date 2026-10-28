"""Lane-owned additive ledger overlay; calls the unchanged NCZ invariant validator.
The NCZ full recomputation CLI accepts its frozen merged index only, so this
records structural validation separately from adoption into that index.
"""
from pathlib import Path
import json,hashlib,importlib.util,collections
E=Path(__file__).resolve().parent;R=E.parent.parent
base=R/'evidence/native-compledger-20261028/NCZ_LEDGER.json'
d=json.loads(base.read_text());inv=json.loads((E/'NDG_INVENTORY.json').read_text())
rows=[('OwnedAccount::owner','owned',3,4,'NDG_MetadataBridge.owner','bytes Err InvalidAccountData; length Ok arbitrary; arbitrary key/owner/flags'),('OwnedAccount::key','owned',5,6,'NDG_MetadataBridge.key','bytes Err InvalidAccountData; length Ok arbitrary; arbitrary key/owner/flags'),('readonly_buffer_meta_ok','adapter',13,14,'NDG_MetadataBridge.buffer','all three Bool inputs; exact ProgramError/Unit lift'),('OwnedAccount::data_len','owned',22,23,'NDG_IdentityLaws.length_success','length Ok arbitrary usize; bytes Err InvalidAccountData'),('OwnedAccount::data','owned',29,30,'NDG_IdentityLaws.data_reference','bytes Ok singleton vector; all byte values; length Ok arbitrary or Err Custom'),('readonly_meta_ok','adapter',15,16,'NDG_MetadataBridge.metadata','all canonical Pubkeys and flags; cohort op36 comparison equals native byte comparison'),('pool_program_id','adapter',9,10,'NDG_IdentityLaws.pool_slot','32-byte return; op45 represented by E001 pool_id_ref; selected installation association retained'),('registry_program_id','adapter',11,12,'NDG_IdentityLaws.registry_slot','32-byte return; op46 represented by E001 registry_id_ref; selected installation association retained')]
closures=[]
for suffix,which,pos,neg,theorem,domain in rows:
 f='programs/r1-cost-probe/src/r1_pool_adapter'+('_owned' if which=='owned' else '')+'.rs::'+suffix
 ids=[f'NDG_K{n:03}' for n in [pos,neg]]
 receipts=[json.loads((E/a/'receipt.json').read_text()) for a in ids]
 assert receipts[0]['exit_status']==0 and receipts[1]['exit_status']!=0
 assert 'VERIFICATION:- SUCCESSFUL' in (E/ids[0]/'stdout.log').read_text()
 assert 'Failed to match' not in (E/ids[1]/'stdout.log').read_text()
 assert 'timed out' not in (E/ids[1]/'stdout.log').read_text()
 cid='NDG::'+suffix;hyp=[dict(name='NDG.PacketDomain',statement=domain,discharged_by=None),dict(name='NDG.PhysicalInterpretation',statement='Same native/cohort input carrier, reference extraction and owner-approved P6/D188 contract semantic transport; caller/installed-dictionary association remains explicit.',discharged_by=None)]
 paths=[str((E/a/'receipt.json').relative_to(R)) for a in ids]
 paths+=[str((E/a/'stdout.log').relative_to(R)) for a in ids]
 paths+=[str((E/(a+'-graph-check.json')).relative_to(R)) for a in ids]
 paths += ['evidence/native-front4-20261028/NDG_FRONTIER_BRIDGES.md']
 for p in paths:
  b=(R/p).read_bytes();d['evidence_manifest'][p]={'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
 claim=dict(claim_id=cid,function=f,admissible_local_credit=True,quarantined_support=[],feature_parity='deployed PROGRAM pool-adapter/private-leaf-salts; full resolved lists in per-attempt graph receipts',named_hypotheses=hyp,evidence=paths,receipts=paths[:2],medium='Kani contract + NCO-pinned reference extraction + Lean equation',source_claim_text=domain,reported_status='CLOSED-CONDITIONAL',limitations='Local domain only. No caller, whole SDK, ELF rebuild, or headline soundness closure.',composition_trust='P6/D188 native contract semantic transport reclassification, not removal')
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
d['NDG_overlay']={'baseline_sha256':hashlib.sha256(base.read_bytes()).hexdigest(),'scope':'local conditional evidence only; baseline critical_path graph retained as historical ranking, not recomputed or adopted','closures':closures}
(E/'NDG_LEDGER.json').write_text(json.dumps(d,indent=2)+'\n')
(E/'NDG_LEDGER_DELTA.json').write_text(json.dumps(dict(schema_version=1,baseline=str(base.relative_to(R)),closures=closures,open=[r['representative'] for r in inv if r['representative'] not in {c['function'] for c in closures}],composed_status='OPEN'),indent=2)+'\n')
spec=importlib.util.spec_from_file_location('NCZ_validate',R/'evidence/native-compledger-20261028/NCZ_validate.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);m.validate_invariants(d)
(E/'NDG_LEDGER_VALIDATION.json').write_text(json.dumps(dict(exit_status=0,validator='unchanged NCZ_validate.py::validate_invariants',validator_sha256=hashlib.sha256((R/'evidence/native-compledger-20261028/NCZ_validate.py').read_bytes()).hexdigest(),ledger_sha256=hashlib.sha256((E/'NDG_LEDGER.json').read_bytes()).hexdigest(),local_conditional=len(closures),composed_closed=0,full_index_recomputation=False),indent=2)+'\n')
print('NCZ invariants PASS; 8 local conditional domains; 0 composed closures')
