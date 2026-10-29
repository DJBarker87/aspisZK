"""Additive local certificate overlay. Uses the unchanged NCZ invariant validator.
Full NCZ collect() is intentionally not changed: its merged snapshot is frozen.
"""
from pathlib import Path
import json,hashlib,importlib.util,collections,sys
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parent.parent
base=R/'evidence/native-compledger-20261028/NCZ_LEDGER.json'
d=json.loads(base.read_text());certs=json.loads((E/'NDH_CERTIFICATES.json').read_text());inv=json.loads((E/'NDH_INVENTORY.json').read_text())
sha=lambda b:hashlib.sha256(b).hexdigest()
claims_by_function={};closures=[]
for c in certs:
 if c['status']!='CLOSED-CONDITIONAL':continue
 f=c['function'];ids=c['kani'];receipts=[json.loads((E/a/'receipt.json').read_text()) for a in ids]
 assert receipts[0]['exit_status']==0 and receipts[1]['exit_status']!=0
 assert 'VERIFICATION:- SUCCESSFUL' in (E/ids[0]/'stdout.log').read_text()
 bad=(E/ids[1]/'stdout.log').read_text()
 assert 'Failed to match' not in bad and 'timed out' not in bad and 'unwinding failures' not in bad
 for a in ids:
  g=json.loads((E/(a+'-graph-check.json')).read_text());assert g['graph_matches_frozen'] and g['exact_frozen_selected_graph'];assert g['resolved_features_all_crates']
  assert json.loads((E/(a+'-lock-check.json')).read_text())['unchanged']
 for a in c['lean']:
  r=json.loads((E/a/'receipt.json').read_text());assert r['exit_status']==0
  assert 'sorryAx' not in str(r['print_axioms'])
  for theorem in c['lean'][a]:assert theorem in str(r['print_axioms']),(a,theorem)
 cid='NDH::'+f
 hyp=[dict(name='NDH.PacketDomain',statement=c['domain'],discharged_by=None),dict(name='NDH.PhysicalInterpretation',statement='Same native/cohort byte or record carriers, actual reference extraction and chosen coherent/missing-slot instance; approved P6/D188 native-contract semantic transport. Caller/installed-headline/ABI and runtime SHA value interpretation remain explicit.',discharged_by=None)]
 paths=[]
 for a in ids:
  paths += [str((E/a/n).relative_to(R)) for n in ['receipt.json','stdout.log','NDH_harness.patch']]
  paths += [str((E/(a+'-graph-check.json')).relative_to(R)),str((E/(a+'-lock-check.json')).relative_to(R))]
 for a in c['lean']:paths += [str((E/a/n).relative_to(R)) for n in ['receipt.json','stdout.log']]
 paths += [str((E/c['extraction']/'receipt.json').relative_to(R)),str((E/c['extraction']/'NDH_EXTRACTION_PINS.json').relative_to(R)),str((E/'NDH_SOURCE_ASSOCIATION.json').relative_to(R)),str((E/'NDH_FRONTIER_BRIDGES.md').relative_to(R))]
 if 'LPk' in c['method']:paths += [str((E/'NDH_INTEGER_REUSE.json').relative_to(R))]
 for p in paths:
  b=(R/p).read_bytes();d['evidence_manifest'][p]={'sha256':sha(b),'bytes':len(b)}
 receipt_paths=[str((E/a/'receipt.json').relative_to(R)) for a in ids]
 claim=dict(claim_id=cid,function=f,admissible_local_credit=True,quarantined_support=[],feature_parity='Every resolved crate pinned per attempt; deployed verifier/program/statement selections. Core gates have exactly the same aspis-core r0 feature set as the deployed verifier.',named_hypotheses=hyp,evidence=paths,receipts=receipt_paths,medium=c['method'],source_claim_text=c['domain'],reported_status='CLOSED-CONDITIONAL',limitations=c['limits']+' Local domain only; enclosing caller and physical/ABI/source-to-ELF remain OPEN.',composition_trust='Owner amendment fifth: P6/D188 native-contract semantic transport reclassification, never premise removal')
 d['claims'].append(claim);claims_by_function[f]=claim
 for r in d['rows']:
  if r['function']!=f:continue
  r.update(bridge_status='CLOSED-CONDITIONAL',selected_claims=[cid],named_hypotheses=hyp,feature_parity_summary=claim['feature_parity'],no_credit_reason=None)
  r['claim_ids'].append(cid);r['evidence']+=paths;r['receipts']+=receipt_paths
  for p in receipt_paths:r['receipt_sha256'][p]=d['evidence_manifest'][p]['sha256']
 closures.append(c)
for tx in ['TX1','TX2','all_rows']:
 chosen=[r for r in d['rows'] if tx=='all_rows' or r['transaction']==tx]
 d['coverage'][tx]['local_bridge_status']=dict(collections.Counter(r['bridge_status'] for r in chosen))
status_by_function={r['function']:r['bridge_status'] for r in d['rows']}
d['coverage']['unique_functions']['local_bridge_status']=dict(collections.Counter(status_by_function.values()))
for r in d['rows']:
 for o in r['caller_domain_obligations']:
  f=o.get('callee')
  if f in status_by_function:o['callee_local_status']=status_by_function[f]
  if f in claims_by_function:
   c=claims_by_function[f];o['callee_claims']=[c['claim_id']];o['required_named_hypotheses']=[h['name'] for h in c['named_hypotheses']]
   o['owner_packets']=sorted(set(o.get('owner_packets',[])+['NDH']))
d['NDH_overlay']={'baseline_sha256':sha(base.read_bytes()),'scope':'Local conditional evidence only. Baseline critical_path and open_transitive_dependencies remain historical conservative discovery/ranking, not recomputed or adopted. No caller-domain discharge or composed closure.','closures':closures}
(E/'NDH_LEDGER.json').write_text(json.dumps(d,indent=2)+'\n')
(E/'NDH_LEDGER_DELTA.json').write_text(json.dumps(dict(schema_version=1,baseline=str(base.relative_to(R)),baseline_sha256=sha(base.read_bytes()),closures=closures,open=[r['representative'] for r in inv if r['representative'] not in claims_by_function],composed_status='OPEN',slot_correction='immutable26/28; paused25/27; activeV2 op29, activeV1 op30; digest/error43/44',trust='P6/D188 native-contract semantic transport reclassification, not removal'),indent=2)+'\n')
v=R/'evidence/native-compledger-20261028/NCZ_validate.py';spec=importlib.util.spec_from_file_location('NCZ_validate',v);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);m.validate_invariants(d)
(E/'NDH_LEDGER_VALIDATION.json').write_text(json.dumps(dict(exit_status=0,validator='unchanged NCZ_validate.py::validate_invariants',validator_sha256=sha(v.read_bytes()),ledger_sha256=sha((E/'NDH_LEDGER.json').read_bytes()),local_conditional=len(closures),composed_closed=0,full_index_recomputation=False,reason='NCZ collect() has a fixed historical report corpus; lead adoption/refresh is required for a full merged-index recomputation.'),indent=2)+'\n')
print('NCZ invariants PASS;',len(closures),'local conditional domains; 0 composed closures')
